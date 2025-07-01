/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for elaborating MACRO_BV_* proof rewrites.
 */

#include "theory/bv/macro_rewrite_elaborator.h"

#include "expr/aci_norm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

MacroRewriteElaborator::MacroRewriteElaborator(Env& env) : EnvObj(env) {}
MacroRewriteElaborator::~MacroRewriteElaborator() {}
bool MacroRewriteElaborator::ensureProofFor(CDProof* cdp,
                                            ProofRewriteRule id,
                                            const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("bv-rew-elab") << "ensureProofFor: " << id << " " << eq << std::endl;
  switch (id)
  {
    case ProofRewriteRule::MACRO_BV_OR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY:
      return ensureProofForSimplify(cdp, eq);
    case ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE:
    case ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE:
      return ensureProofForConcatMerge(cdp, id, eq);
    case ProofRewriteRule::MACRO_BV_EXTRACT_CONCAT:
      return ensureProofForExtractConcat(cdp, eq);
    case ProofRewriteRule::MACRO_BV_MULT_SLT_MULT:
      return ensureProofForMultSltMult(cdp, eq);
    case ProofRewriteRule::MACRO_BV_AND_OR_XOR_CONCAT_PULLUP:
      return ensureProofForAndOrXorConcatPullup(cdp, eq);
    default: break;
  }
  return false;
}

bool MacroRewriteElaborator::ensureProofForSimplify(CDProof* cdp,
                                                    const Node& eq)
{
  // below, we group all of the constant children into one nested
  // child, prove the grouping by ACI_NORM, evaluate the constant
  // child, then prove the equality by another instance of ACI_NORM
  // if necessary.
  NodeManager* nm = nodeManager();
  Kind k = eq[0].getKind();
  std::vector<Node> consts;
  std::vector<Node> nconsts;
  for (const Node& cc : eq[0])
  {
    if (cc.isConst())
    {
      consts.push_back(cc);
    }
    else
    {
      nconsts.push_back(cc);
    }
  }
  if (consts.size() <= 1 || nconsts.empty())
  {
    Assert(false) << "BV simplify: no constant eval";
    return false;
  }
  std::vector<Node> transEq;
  Node cc = nm->mkNode(k, consts);
  nconsts.insert(nconsts.begin(), cc);
  Node eq0c = nm->mkNode(k, nconsts);
  Node equiv1 = eq[0].eqNode(eq0c);
  cdp->addStep(equiv1, ProofRule::ACI_NORM, {}, {equiv1});
  transEq.push_back(equiv1);
  Node ccr = evaluate(cc, {}, {});
  Node ceq = cc.eqNode(ccr);
  cdp->addTrustedStep(ceq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  std::vector<Node> premises;
  premises.push_back(ceq);
  Node equiv2 = proveCong(cdp, eq0c, premises);
  Assert(equiv2.getKind() == Kind::EQUAL);
  transEq.push_back(equiv2);
  if (equiv2[1] != eq[1])
  {
    // could be ACI_NORM or ABSORB, just send generic subgoal.
    Node equiv3 = equiv2[1].eqNode(eq[1]);
    cdp->addTrustedStep(
        equiv3, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(equiv3);
  }
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool MacroRewriteElaborator::ensureProofForConcatMerge(CDProof* cdp,
                                                       ProofRewriteRule id,
                                                       const Node& eq)
{
  // below, we group portions of the concatenation into a form in which they
  // can be rewritten in isolation. We prove the grouping by ACI_NORM, then
  // prove the individual rewrites by either a RARE rule for ConcatExtractMerge
  // (if merging extracts) or by evaluate (if merging constants).
  NodeManager* nm = nodeManager();
  Node concat = eq[0];
  std::vector<Node> children;
  std::vector<Node> curr;
  Node currRew;
  Kind ck = Kind::UNDEFINED_KIND;
  TConvProofGenerator tcpg(d_env);
  for (size_t i = 0, nchild = concat.getNumChildren(); i <= nchild; i++)
  {
    Node next = i < nchild ? concat[i] : Node::null();
    bool merged = false;
    if (!curr.empty() && next.getKind() == ck
        && ((ck == Kind::CONST_BITVECTOR
             && id == ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE)
            || (ck == Kind::BITVECTOR_EXTRACT
                && id == ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE)))
    {
      if (ck == Kind::BITVECTOR_EXTRACT)
      {
        Assert(curr.size() == 1);
        curr[0] = nm->mkNode(Kind::BITVECTOR_CONCAT, curr[0], next);
        currRew = nm->mkNode(Kind::BITVECTOR_CONCAT, currRew, next);
        Node rcr = RewriteRule<ConcatExtractMerge>::run<true>(currRew);
        if (rcr != currRew)
        {
          Trace("bv-rew-elab")
              << "- r-step: " << currRew << " " << rcr << std::endl;
          // single rewrite step
          tcpg.addRewriteStep(currRew,
                              rcr,
                              nullptr,
                              false,
                              TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
          currRew = rcr;
          merged = true;
        }
        else
        {
          // an adjacent extract, but one that did not merge
          curr[0] = currRew[0];
        }
      }
      else
      {
        Assert(ck == Kind::CONST_BITVECTOR);
        curr.push_back(next);
        merged = true;
      }
    }
    if (!merged)
    {
      if (!curr.empty())
      {
        Node rem;
        if (curr.size() > 1)
        {
          rem = nm->mkNode(Kind::BITVECTOR_CONCAT, curr);
          Node rr = evaluate(rem, {}, {});

          tcpg.addRewriteStep(rem, rr, ProofRule::EVALUATE, {}, {rem});
        }
        else
        {
          rem = curr[0];
        }
        children.push_back(rem);
        curr.clear();
      }
      curr.push_back(next);
      currRew = next;
      ck = next.getKind();
    }
  }
  Node gc = children.size() == 1 ? children[0]
                                 : nm->mkNode(Kind::BITVECTOR_CONCAT, children);
  Node equiv1 = eq[0].eqNode(gc);
  Trace("bv-rew-elab") << "- grouped concat: " << equiv1 << std::endl;
  cdp->addStep(equiv1, ProofRule::ACI_NORM, {}, {equiv1});

  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(gc);
  cdp->addProof(pfn);
  Node equiv2 = pfn->getResult();
  Trace("bv-rew-elab") << "- rewritten: " << equiv2 << std::endl;
  if (equiv2[1] == eq[1])
  {
    cdp->addStep(eq, ProofRule::TRANS, {equiv1, equiv2}, {});
    return true;
  }
  Assert(false) << "...mismatch " << equiv2[1] << " " << eq[1];
  return false;
}

bool MacroRewriteElaborator::ensureProofForExtractConcat(CDProof* cdp,
                                                         const Node& eq)
{
  // Below, we curry the bvconcat and then apply ExtractConcat to each 2
  // argument bv concat in isolation. We prove the currying via ACI_NORM and
  // then prove the result (which is curried) is equivalent to the right hand
  // side with another application of ACI_NORM.
  NodeManager* nm = nodeManager();
  Assert(eq[0].getKind() == Kind::BITVECTOR_EXTRACT);
  Node concat = eq[0][0];
  Assert(concat.getKind() == Kind::BITVECTOR_CONCAT);
  Node curr = concat[0];
  Trace("bv-rew-elab") << "concat is " << concat << std::endl;
  for (size_t i = 1, nchild = concat.getNumChildren(); i < nchild; i++)
  {
    curr = nm->mkNode(Kind::BITVECTOR_CONCAT, curr, concat[i]);
  }
  Node ceq = concat.eqNode(curr);
  Trace("bv-rew-elab") << "  - grouped concat: " << ceq << std::endl;
  cdp->addStep(ceq, ProofRule::ACI_NORM, {}, {ceq});
  std::vector<Node> transEq;
  Node equiv1 = proveCong(cdp, eq[0], {ceq});
  transEq.push_back(equiv1);
  Trace("bv-rew-elab") << "- grouped extract-concat: " << equiv1 << std::endl;
  Assert(equiv1.getKind() == Kind::EQUAL);
  Node exc = equiv1[1];
  TConvProofGenerator tcpg(d_env);
  while (RewriteRule<ExtractConcat>::applies(exc))
  {
    Node excr = RewriteRule<ExtractConcat>::run<false>(exc);
    Trace("bv-rew-elab") << "  - rewrite: " << exc << " -> " << excr
                         << std::endl;
    Assert(exc != excr);
    // single rewrite step
    tcpg.addRewriteStep(
        exc, excr, nullptr, true, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
    if (excr.getKind() == Kind::BITVECTOR_EXTRACT)
    {
      exc = excr;
    }
    else if (excr.getKind() == Kind::BITVECTOR_CONCAT)
    {
      Assert(excr.getNumChildren() == 2);
      exc = excr[0];
    }
    else
    {
      break;
    }
  }

  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(equiv1[1]);
  cdp->addProof(pfn);
  Node equiv2 = pfn->getResult();
  transEq.push_back(equiv2);
  Trace("bv-rew-elab") << "- grouped concat: " << equiv2 << std::endl;
  if (equiv2[1] != eq[1])
  {
    if (expr::isACINorm(equiv2[1], eq[1]))
    {
      Node equiv3 = equiv2[1].eqNode(eq[1]);
      cdp->addStep(equiv3, ProofRule::ACI_NORM, {}, {equiv3});
      transEq.push_back(equiv3);
    }
    else
    {
      return false;
    }
  }
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool MacroRewriteElaborator::ensureProofForMultSltMult(CDProof* cdp,
                                                       const Node& eq)
{
  // the rewrites below ensure we match the form of RARE rewrites
  // bv-mult-slt-mult-1 and bv-mult-slt-mult-2 by turning concatenation
  // with zero into a zero extend, and flipping multiplication if applicable.
  NodeManager* nm = nodeManager();
  Assert(eq[0].getKind() == Kind::BITVECTOR_SLT);
  TConvProofGenerator tcpg(d_env);
  Node rhs1;
  for (size_t i = 0; i < 2; i++)
  {
    Assert(eq[0][i].getKind() == Kind::BITVECTOR_MULT);
    Assert(eq[0][i].getNumChildren() == 2);
    std::vector<Node> ch;
    for (size_t j = 0; j < 2; j++)
    {
      Node n = eq[0][i][j];
      if (n.getKind() == Kind::BITVECTOR_CONCAT)
      {
        size_t sz = utils::getSize(n[0]);
        if (n[0] == utils::mkZero(nm, sz))
        {
          // turn concatenation with zero into zero extend
          Node zext = nm->mkConst(BitVectorZeroExtend(sz));
          Node nze = nm->mkNode(zext, n[1]);
          tcpg.addRewriteStep(n,
                              nze,
                              nullptr,
                              false,
                              TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
          ch.push_back(nze);
          continue;
        }
      }
      ch.push_back(n);
    }
    // flip the multiplication on the right hand side if a zero_extend
    // or a sign_extend applied to plus. Flip the left hand side if the
    // lhs of the left hand side matches the rhs of the right hand side.
    bool swap = i == 0 ? (ch[1].getKind() == Kind::BITVECTOR_ZERO_EXTEND
                          || (ch[1].getKind() == Kind::BITVECTOR_SIGN_EXTEND
                              && ch[1][0].getKind() == Kind::BITVECTOR_ADD))
                       : ch[0] == rhs1;
    Trace("bv-rew-elab") << "- check " << i << ", swap is " << swap
                         << std::endl;
    if (swap)
    {
      Assert(ch[0].getKind() != Kind::BITVECTOR_ZERO_EXTEND);
      // swap to match rule
      Node mul = nm->mkNode(eq[0][i].getKind(), ch[0], ch[1]);
      Node muls = nm->mkNode(eq[0][i].getKind(), ch[1], ch[0]);
      tcpg.addRewriteStep(mul,
                          muls,
                          nullptr,
                          false,
                          TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
      Trace("bv-rew-elab") << "- swap " << mul << " to " << muls << std::endl;
    }
    if (i == 0)
    {
      rhs1 = ch[swap ? 0 : 1];
      Trace("bv-rew-elab") << "- rhs is " << rhs1 << std::endl;
    }
  }

  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
  cdp->addProof(pfn);
  Node equiv1 = pfn->getResult();
  Trace("bv-rew-elab") << "- cast to zero extend: " << equiv1 << std::endl;
  Node equiv2 = equiv1[1].eqNode(eq[1]);
  cdp->addTrustedStep(
      equiv2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(eq, ProofRule::TRANS, {equiv1, equiv2}, {});
  return true;
}

bool MacroRewriteElaborator::ensureProofForAndOrXorConcatPullup(CDProof* cdp,
                                                                const Node& eq)
{
  // The elaboration below handles the case where a constant appears in the
  // middle of a concatenation term that is being pulled up.
  // (bvor xs (concat t1 ... tn c s1 ... sm) ws) ---> (concat ...)
  // This method groups the concatenation term so that it matches the expected
  // form of RARE rewrites bv-*-concat-pullup3. In particular we rewrite:
  // (bvor xs (concat t1 ... tn c s1 ... sm) ws) --->
  // (bvor xs (concat (concat t1 ... tn) c (concat s1 ... sm)) ws).
  NodeManager* nm = nodeManager();
  TConvProofGenerator tcpg(d_env);
  bool addedRewrite = false;
  for (const TNode& c : eq[0])
  {
    if (c.getKind() == Kind::BITVECTOR_CONCAT)
    {
      for (size_t i = 0, nchild = c.getNumChildren(); i < nchild; i++)
      {
        if (c[i].isConst() && i > 0 && i + 1 < nchild)
        {
          std::vector<Node> cpre(c.begin(), c.begin() + i);
          Node npre = cpre.size() == 1
                          ? cpre[0]
                          : nm->mkNode(Kind::BITVECTOR_CONCAT, cpre);
          std::vector<Node> cpost(c.begin() + i + 1, c.end());
          Node npost = cpost.size() == 1
                           ? cpost[0]
                           : nm->mkNode(Kind::BITVECTOR_CONCAT, cpost);
          Node cg = nm->mkNode(Kind::BITVECTOR_CONCAT, {npre, c[i], npost});
          Trace("ajr-temp") << "Groupd " << c << " to " << cg << std::endl;
          Assert(cg.getType() == c.getType());
          // should be shown by ACI_NORM
          tcpg.addRewriteStep(c,
                              cg,
                              nullptr,
                              false,
                              TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
          addedRewrite = true;
          break;
        }
      }
    }
  }
  if (!addedRewrite)
  {
    Assert(false) << "Failed to elaborate and-or-xor-concat-pullup";
    return false;
  }
  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
  cdp->addProof(pfn);
  Node equiv1 = pfn->getResult();
  Node equiv2 = equiv1[1].eqNode(eq[1]);
  // should be shown by bv-*-concat-pullup3
  cdp->addTrustedStep(
      equiv2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(eq, ProofRule::TRANS, {equiv1, equiv2}, {});
  return true;
}

Node MacroRewriteElaborator::proveCong(CDProof* cdp,
                                       const Node& n,
                                       const std::vector<Node>& premises)
{
  std::vector<Node> cpremises = premises;
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(n, cargs);
  cpremises.resize(n.getNumChildren());
  // add REFL if a premise is not provided
  for (size_t i = 0, npremises = cpremises.size(); i < npremises; i++)
  {
    if (cpremises[i].isNull())
    {
      Node refl = n[i].eqNode(n[i]);
      cdp->addStep(refl, ProofRule::REFL, {}, {n[i]});
      cpremises[i] = refl;
    }
  }
  Trace("brc-macro") << "- cong " << cr << " " << cpremises << " " << cargs
                     << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node eq = pc->checkDebug(cr, cpremises, cargs);
  Trace("brc-macro") << "...returns " << eq << std::endl;
  if (!eq.isNull())
  {
    cdp->addStep(eq, cr, cpremises, cargs);
  }
  return eq;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

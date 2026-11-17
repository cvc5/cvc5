/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "rewriter/basic_rewrite_rcons.h"

#include "expr/aci_norm.h"
#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "expr/term_context.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "rewriter/rewrite_db_term_process.h"
#include "rewriter/rewrites.h"
#include "smt/env.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_proof_utilities.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/rewriter/rewrite_atom.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

std::ostream& operator<<(std::ostream& os, TheoryRewriteMode tm)
{
  switch (tm)
  {
    case TheoryRewriteMode::STANDARD: return os << "STANDARD";
    case TheoryRewriteMode::RESORT: return os << "RESORT";
    case TheoryRewriteMode::NEVER: return os << "NEVER";
  }
  Unreachable();
  return os;
}

BasicRewriteRCons::BasicRewriteRCons(Env& env)
    : EnvObj(env),
      d_theoryRewriteMacroExpand(
          statisticsRegistry().registerHistogram<ProofRewriteRule>(
              "BasicRewriteRCons::macroExpandCount")),
      d_bvRewElab(env),
      d_strRewElab(env)
{
}

bool BasicRewriteRCons::prove(CDProof* cdp,
                              Node a,
                              Node b,
                              TheoryRewriteMode tmode)
{
  Node eq = a.eqNode(b);
  Trace("trewrite-rcons") << "Reconstruct " << eq << std::endl;
  // this probably should never happen
  if (eq[0] == eq[1])
  {
    Trace("trewrite-rcons") << "...REFL" << std::endl;
    cdp->addStep(eq, ProofRule::REFL, {}, {eq[0]});
    return true;
  }
  // first, check that maybe its just an evaluation step
  if (tryRule(cdp, eq, ProofRule::EVALUATE, {eq[0]}))
  {
    Trace("trewrite-rcons") << "...EVALUATE" << std::endl;
    return true;
  }

  // if (= (= c1 c2) false) where c1, c2 are distinct values
  if (a.getKind() == Kind::EQUAL && a[0].isConst() && a[1].isConst()
      && b.isConst() && !b.getConst<bool>())
  {
    Node neq = a[0].eqNode(a[1]).notNode();
    cdp->addStep(neq, ProofRule::DISTINCT_VALUES, {}, {a[0], a[1]});
    cdp->addStep(eq, ProofRule::FALSE_INTRO, {neq}, {});
    Trace("trewrite-rcons") << "...DISTINCT_VALUES" << std::endl;
    return true;
  }

  // try theory rewrite (pre-rare)
  if (tmode == TheoryRewriteMode::STANDARD)
  {
    if (tryTheoryRewrite(cdp, eq, theory::TheoryRewriteCtx::PRE_DSL))
    {
      Trace("trewrite-rcons")
          << "Reconstruct (pre) " << eq << " via theory rewrite" << std::endl;
      return true;
    }
  }
  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::postProve(CDProof* cdp,
                                  Node a,
                                  Node b,
                                  TheoryRewriteMode tmode)
{
  Node eq = a.eqNode(b);
  // try theory rewrite (post-rare), which may try both pre and post if
  // the proof-granularity mode is dsl-rewrite-strict.
  bool success = false;
  if (tmode == TheoryRewriteMode::RESORT)
  {
    if (tryTheoryRewrite(cdp, eq, theory::TheoryRewriteCtx::PRE_DSL))
    {
      success = true;
    }
  }
  if (!success && tmode != TheoryRewriteMode::NEVER
      && tryTheoryRewrite(cdp, eq, theory::TheoryRewriteCtx::POST_DSL))
  {
    success = true;
  }
  if (success)
  {
    Trace("trewrite-rcons")
        << "Reconstruct (post) " << eq << " via theory rewrite" << std::endl;
  }
  else
  {
    Trace("trewrite-rcons") << "...(fail)" << std::endl;
  }
  return success;
}

bool BasicRewriteRCons::tryRule(CDProof* cdp,
                                Node eq,
                                ProofRule r,
                                const std::vector<Node>& args,
                                bool addStep)
{
  Trace("trewrite-rcons-debug") << "Try " << r << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  // do not provide expected, as this will always succeed if proof checking
  // is disabled
  Node res = pc->checkDebug(r, {}, args, Node::null(), "trewrite-rcons");
  if (!res.isNull() && res == eq)
  {
    if (addStep)
    {
      cdp->addStep(eq, r, {}, args);
    }
    return true;
  }
  return false;
}

void BasicRewriteRCons::ensureProofForEncodeTransform(CDProof* cdp,
                                                      const Node& eq,
                                                      const Node& eqi)
{
  ProofRewriteDbNodeConverter rdnc(d_env);
  std::shared_ptr<ProofNode> pfn = rdnc.convert(eq);
  Node equiv = eq.eqNode(eqi);
  Assert(pfn->getResult() == equiv);
  cdp->addProof(pfn);
  Node equivs = eqi.eqNode(eq);
  cdp->addStep(equivs, ProofRule::SYMM, {equiv}, {});
  cdp->addStep(eq, ProofRule::EQ_RESOLVE, {eqi, equivs}, {});
}

void BasicRewriteRCons::ensureProofForTheoryRewrite(CDProof* cdp,
                                                    ProofRewriteRule id,
                                                    const Node& eq)
{
  bool handledMacro = false;
  switch (id)
  {
    case ProofRewriteRule::MACRO_BOOL_NNF_NORM:
      if (ensureProofMacroBoolNnfNorm(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_BOOL_EQ_CONST_EQ:
      if (ensureProofMacroBoolEqConstEq(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_BOOL_BV_INVERT_SOLVE:
      if (ensureProofMacroBoolBvInvertSolve(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_ARITH_INT_EQ_CONFLICT:
    case ProofRewriteRule::MACRO_ARITH_INT_GEQ_TIGHTEN:
      if (ensureProofMacroArithIntRelation(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_DT_CONS_EQ:
      if (ensureProofMacroDtConsEq(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
    case ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION:
    case ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM:
    case ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH:
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX:
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY:
    case ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS:
    case ProofRewriteRule::MACRO_STR_SPLIT_CTN:
    case ProofRewriteRule::MACRO_STR_COMPONENT_CTN:
    case ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT:
    case ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION:
      handledMacro = d_strRewElab.ensureProofFor(cdp, id, eq);
      break;
    case ProofRewriteRule::MACRO_QUANT_MERGE_PRENEX:
      if (ensureProofMacroQuantMergePrenex(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_PRENEX:
      if (ensureProofMacroQuantPrenex(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_PARTITION_CONNECTED_FV:
      if (ensureProofMacroQuantPartitionConnectedFv(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_VAR_ELIM_EQ:
      if (ensureProofMacroQuantVarElimEq(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_DT_VAR_EXPAND:
      if (ensureProofMacroDtVarExpand(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_MINISCOPE:
      if (ensureProofMacroQuantMiniscope(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_QUANT_REWRITE_BODY:
      if (ensureProofMacroQuantRewriteBody(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_BV_EQ_SOLVE:
      if (ensureProofMacroBvEqSolve(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_LAMBDA_CAPTURE_AVOID:
    case ProofRewriteRule::MACRO_QUANT_ELIM_SHADOW:
      if (ensureProofMacroElimShadow(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_ARRAYS_NORMALIZE_OP:
      if (ensureProofMacroArraysNormalizeOp(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_BV_EXTRACT_CONCAT:
    case ProofRewriteRule::MACRO_BV_OR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_OR_XOR_CONCAT_PULLUP:
    case ProofRewriteRule::MACRO_BV_MULT_SLT_MULT:
    case ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE:
    case ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE:
      handledMacro = d_bvRewElab.ensureProofFor(cdp, id, eq);
      break;
    default: break;
  }
  if (handledMacro)
  {
    d_theoryRewriteMacroExpand << id;
    Trace("brc-macro-debug")
        << "Proof is " << *cdp->getProofFor(eq) << std::endl;
    return;
  }
  // default, just add the rewrite
  std::vector<Node> args;
  args.push_back(
      nodeManager()->mkConstInt(Rational(static_cast<uint32_t>(id))));
  args.push_back(eq);
  // always overwrite, in case we partially completed a proof in a macro method
  // above
  cdp->addStep(
      eq, ProofRule::THEORY_REWRITE, {}, args, false, CDPOverwrite::ALWAYS);
}

bool BasicRewriteRCons::ensureProofMacroBoolNnfNorm(CDProof* cdp,
                                                    const Node& eq)
{
  Trace("brc-macro") << "Expand Bool NNF norm " << eq[0] << " == " << eq[1]
                     << std::endl;
  // Call the utility again with proof tracking and construct the term
  // conversion proof. This proof itself may have trust steps in it.
  // Rewrites should only be applied for terms in the Boolean skeleton, hence
  // we use BoolSkeletonTermContext here.
  BoolSkeletonTermContext bstc;
  TConvProofGenerator tcpg(d_env,
                           nullptr,
                           TConvPolicy::FIXPOINT,
                           TConvCachePolicy::NEVER,
                           "MacroNnfNormTConv",
                           &bstc);
  Node nr = theory::booleans::TheoryBoolRewriter::computeNnfNorm(
      nodeManager(), eq[0], &tcpg);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(eq);
  Trace("brc-macro") << "...proof is " << *pfn.get() << std::endl;
  cdp->addProof(pfn);
  return true;
}

bool BasicRewriteRCons::ensureProofMacroBoolEqConstEq(CDProof* cdp,
                                                      const Node& eq)
{
  Trace("brc-macro") << "Expand Bool eq const eq " << eq[0] << " == " << eq[1]
                     << std::endl;
  Assert(eq[0].getKind() == Kind::EQUAL);
  Assert(eq[0][0].getKind() == Kind::EQUAL
         && eq[0][1].getKind() == Kind::EQUAL);
  if (eq[0][0] == eq[0][1])
  {
    // true case is handled by RARE rule eq-refl
    cdp->addTrustedStep(eq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    return true;
  }
  // orient the equalities properly
  std::vector<Node> premises;
  for (size_t i = 0; i < 2; i++)
  {
    // flip if constant is on the left side
    if (eq[0][i][0].isConst())
    {
      Node sym = eq[0][i][1].eqNode(eq[0][i][0]);
      Node eqq = eq[0][i].eqNode(sym);
      // will prove equality between equality and flipped form
      cdp->addTrustedStep(
          eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      premises.push_back(eqq);
    }
    else
    {
      premises.push_back(Node::null());
    }
  }
  Node equiv1 = proveCong(cdp, eq[0], premises);
  Trace("brc-macro") << "...orient LHS via " << equiv1 << std::endl;
  if (equiv1[0] == equiv1[1])
  {
    // no flipping was necessary, should be RARE rule eq-cond-deq
    cdp->addTrustedStep(eq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    return true;
  }
  Node equiv2 = equiv1[1].eqNode(eq[1]);
  // should be proven by RARE rule eq-cond-deq
  cdp->addTrustedStep(
      equiv2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(eq, ProofRule::TRANS, {equiv1, equiv2}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroBoolBvInvertSolve(CDProof* cdp,
                                                          const Node& eq)
{
  Trace("brc-macro") << "Expand Bool BV invert solve " << eq[0]
                     << " == " << eq[1] << std::endl;
  Assert(eq[0].getKind() == Kind::EQUAL);
  Assert(eq[0][0].getKind() == Kind::EQUAL
         && eq[0][1].getKind() == Kind::EQUAL);
  // Use the same disallowed kinds as the rewrite (see rewriteViaRule for
  // MACRO_BOOL_BV_INVERT_SOLVE), so that proof reconstruction matches the
  // solving that was actually performed by the rewrite.
  std::unordered_set<Kind> disallowedKinds;
  disallowedKinds.insert(Kind::BITVECTOR_CONCAT);
  theory::booleans::TheoryBoolRewriter::getBvInvertSolve(
      nodeManager(), eq[0][0], eq[0][1][0], disallowedKinds, cdp);
  // finish proof
  cdp->addStep(eq, ProofRule::TRUE_INTRO, {eq[0]}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroArithIntRelation(CDProof* cdp,
                                                         const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("brc-macro") << "Expand int relation for " << eq << std::endl;
  NodeManager* nm = nodeManager();
  Kind rk = eq[0].getKind();
  Assert(rk == Kind::EQUAL || rk == Kind::GEQ);
  Node rewRel = eq[0];
  std::vector<Node> transEq;
  if (rewRel[0].getType().isInteger() && rk == Kind::EQUAL)
  {
    // if we are starting from an integer equality, we should convert to
    // a real equality first to ensure the ARITH_POLY_NORM_REL step will
    // work below.
    Node rer = nm->mkNode(rk,
                          {nm->mkNode(Kind::TO_REAL, rewRel[0]),
                           nm->mkNode(Kind::TO_REAL, rewRel[1])});
    Node eqq = rewRel.eqNode(rer);
    cdp->addTrustedStep(
        eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(eqq);
    rewRel = rer;
  }
  // construct the setup equality
  std::pair<Node, Node> p =
      theory::arith::rewriter::decomposeRelation(nm, rewRel[0], rewRel[1]);
  Assert(p.second.isConst());
  Assert(!p.second.getConst<Rational>().isIntegral());
  Node iterm = p.first;
  if (p.first.getType().isReal())
  {
    Trace("brc-macro") << "Real term convert to integer: " << p.first
                       << std::endl;
    theory::arith::rewriter::Sum sum;
    theory::arith::rewriter::addToSumNoMixed(sum, p.first, false);
    iterm = collectSum(nodeManager(), sum);
    Trace("brc-macro") << "...converts to " << iterm << std::endl;
  }
  Node rewLhs = nm->mkNode(Kind::TO_REAL, iterm);
  Node rew = nm->mkNode(rk, rewLhs, p.second);
  Trace("brc-macro") << "...setup relation is " << rew << std::endl;
  Node eqq = rewRel.eqNode(rew);
  transEq.push_back(eqq);
  // should be able to show the equivalence by ARITH_POLY_NORM_REL
  if (!ensureProofArithPolyNormRel(cdp, eqq))
  {
    Trace("brc-macro") << "...failed arith poly rel" << std::endl;
    return false;
  }
  Node tgt = eq[1];
  // if GEQ, we rewrite the right hand side to match the RARE rule
  // arith-int-geq-tighten verbatim
  if (rk == Kind::GEQ)
  {
    // use the correct type
    Node cceil = nm->mkConstRealOrInt(p.first.getType(),
                                      p.second.getConst<Rational>().ceiling());
    tgt = nm->mkNode(rk, p.first, cceil);
  }
  // the last step can be shown by the RARE rules
  // arith-int-eq-conflict or arith-int-geq-tighten
  eqq = rew.eqNode(tgt);
  Trace("brc-macro") << "...subgoal (1): " << eqq << std::endl;
  cdp->addTrustedStep(eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  transEq.push_back(eqq);
  if (tgt != eq[1])
  {
    eqq = tgt.eqNode(eq[1]);
    Trace("brc-macro") << "...subgoal (2): " << eqq << std::endl;
    cdp->addTrustedStep(
        eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(eqq);
  }
  // connect with transitive
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroDtConsEq(CDProof* cdp, const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("brc-macro") << "Expand dt cons eq for " << eq << std::endl;
  TConvProofGenerator tcpg(d_env);
  theory::Rewriter* rr = d_env.getRewriter();
  if (eq[1].isConst())
  {
    // DT_CONS_EQ_CLASH may suffice if it is purely datatypes
    Node curRew = rr->rewriteViaRule(ProofRewriteRule::DT_CONS_EQ_CLASH, eq[0]);
    if (curRew == eq[1])
    {
      cdp->addTheoryRewriteStep(eq, ProofRewriteRule::DT_CONS_EQ_CLASH);
      return true;
    }
    Assert(eq[0].getKind() == Kind::EQUAL);
    // otherwise, we require proving the non-datatype constants are distinct
    std::vector<size_t> path;
    std::vector<Node> rew;
    theory::datatypes::utils::checkClash(eq[0][0], eq[0][1], rew, true, path);
    Trace("brc-macro") << "clash " << eq[0] << " with path " << path.size()
                       << std::endl;
    Node currEq = eq[0];
    NodeManager* nm = nodeManager();
    Node falsen = nm->mkConst(false);
    for (size_t i = 0, npath = path.size(); i < npath; i++)
    {
      Trace("brc-macro") << "- unify eq " << currEq << std::endl;
      // e.g C(t1...tn)=C(s1...sn) = (and (t1=s1) ... (tn=sn))
      Node currConj = rr->rewriteViaRule(ProofRewriteRule::DT_CONS_EQ, currEq);
      Assert(!currConj.isNull());
      tcpg.addTheoryRewriteStep(currEq, currConj, ProofRewriteRule::DT_CONS_EQ);
      size_t p = path[npath - i - 1];
      Assert(p < currEq[0].getNumChildren());
      Assert(p < currEq[1].getNumChildren());
      if (currConj.getKind() == Kind::AND)
      {
        // (and (t1=s1) ... false .... (tn=sn)) = false
        // should be proven by a RARE rule.
        std::vector<Node> cc(currConj.begin(), currConj.end());
        cc[p] = falsen;
        Node currConjf = nm->mkAnd(cc);
        tcpg.addRewriteStep(currConjf,
                            falsen,
                            nullptr,
                            false,
                            TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
      }
      // recurse
      currEq = currEq[0][p].eqNode(currEq[1][p]);
    }
    // base case, we have a conflicting value.
    // should be proven by evaluation or by an ad-hoc rewrite.
    Trace("brc-macro") << "- conflicting values " << currEq << std::endl;
    Assert(currEq[0].isConst() && currEq[1].isConst()
           && currEq[0] != currEq[1]);
    tcpg.addRewriteStep(currEq,
                        falsen,
                        nullptr,
                        false,
                        TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
  }
  else
  {
    std::unordered_set<TNode> visited;
    std::vector<TNode> visit;
    TNode cur;
    visit.push_back(eq[0]);
    do
    {
      cur = visit.back();
      visit.pop_back();
      if (visited.find(cur) == visited.end())
      {
        visited.insert(cur);
        if (cur.getKind() == Kind::EQUAL)
        {
          // if a reflexive component, it rewrites to true
          if (cur[0] == cur[1])
          {
            Node truen = nodeManager()->mkConst(true);
            tcpg.addRewriteStep(cur,
                                truen,
                                nullptr,
                                true,
                                TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
            continue;
          }
          Node curRew = rr->rewriteViaRule(ProofRewriteRule::DT_CONS_EQ, cur);
          if (!curRew.isNull())
          {
            tcpg.addTheoryRewriteStep(
                cur, curRew, ProofRewriteRule::DT_CONS_EQ, true);
            visit.push_back(curRew);
          }
        }
        else
        {
          // traverse AND
          Assert(cur.getKind() == Kind::AND);
          visit.insert(visit.end(), cur.begin(), cur.end());
        }
      }
    } while (!visit.empty());
  }
  // get proof for rewriting, which should expand equalities
  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
  Node res = pfn->getResult();
  Assert(res.getKind() == Kind::EQUAL);
  // the right hand side should rewrite to the other side
  Node rhs = res[1];
  if (rhs == eq[1])
  {
    // no rewrite needed, e.g. one step
    cdp->addProof(pfn);
    return true;
  }
  // should rewrite via ACI_NORM
  if (!expr::isACINorm(rhs, eq[1]))
  {
    Trace("brc-macro") << "Failed to show " << rhs << " == " << eq[1]
                       << std::endl;
    DebugUnhandled() << "Failed to show " << rhs << " == " << eq[1]
                     << std::endl;
    return false;
  }
  // use ACI_NORM
  cdp->addProof(pfn);
  Node eqa = rhs.eqNode(eq[1]);
  cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa});
  cdp->addStep(eq, ProofRule::TRANS, {res, eqa}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantMergePrenex(CDProof* cdp,
                                                         const Node& eq)
{
  Trace("brc-macro") << "Expand macro quant merge prenex for " << eq
                     << std::endl;
  theory::Rewriter* rr = d_env.getRewriter();
  Node qm = rr->rewriteViaRule(ProofRewriteRule::QUANT_MERGE_PRENEX, eq[0]);
  Trace("brc-macro") << "...non-macro to " << qm << std::endl;
  std::vector<Node> transEq;
  if (!qm.isNull())
  {
    Node equiv = eq[0].eqNode(qm);
    cdp->addTheoryRewriteStep(equiv, ProofRewriteRule::QUANT_MERGE_PRENEX);
    transEq.push_back(equiv);
  }
  else
  {
    qm = eq[0];
  }
  if (qm == eq[1])
  {
    return true;
  }
  // if variables were duplicated, remove them with QUANT_UNUSED_VARS
  Node qmu = rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, qm);
  if (qmu.isNull())
  {
    DebugUnhandled();
    return false;
  }
  Node equiv2 = qm.eqNode(qmu);
  cdp->addTheoryRewriteStep(equiv2, ProofRewriteRule::QUANT_UNUSED_VARS);
  transEq.push_back(equiv2);
  if (qmu != eq[1])
  {
    // May be we removed too many variables, in this case we do the same
    // removal for the opposite side, which should give the same result.
    Node qmu2 = rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, eq[1]);
    if (qmu2 != qmu)
    {
      DebugUnhandled();
      return false;
    }
    Node equiv3 = eq[1].eqNode(qmu2);
    cdp->addTheoryRewriteStep(equiv3, ProofRewriteRule::QUANT_UNUSED_VARS);
    Node equiv3s = qmu2.eqNode(eq[1]);
    cdp->addStep(equiv3s, ProofRule::SYMM, {equiv3}, {});
    transEq.push_back(equiv3s);
  }
  if (transEq.size() > 1)
  {
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  }
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantPrenex(CDProof* cdp,
                                                    const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand macro quant prenex for " << eq << std::endl;
  Assert(eq[0].getKind() == Kind::FORALL);
  Assert(eq[1].getKind() == Kind::FORALL);
  Node body1 = eq[0][1];
  Node body2 = eq[1][1];
  // take the prenexed variables
  size_t nvars1 = eq[0][0].getNumChildren();
  std::vector<Node> newVars(eq[1][0].begin() + nvars1, eq[1][0].end());
  Assert(!newVars.empty());
  Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, newVars);
  body2 = nm->mkNode(Kind::FORALL, bvl, body2);
  Node umergeq = nm->mkNode(Kind::FORALL, eq[0][0], body2);
  Node beq = body1.eqNode(body2);
  // We set up the elaboration as follows:
  //
  // F = forall Y. G
  // ------------------------------- CONG ------------------------ MERGE_PRENEX
  // forall X. F = forall X. forall Y. G   forall X. forall Y. G = forall XY. G
  // --------------------------------------------------------------- TRANS
  // forall X. F = forall XY. G
  //
  // where the free assumption can be proven by miniscoping.
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(eq[0], cargs);
  Node eqq = eq[0].eqNode(umergeq);
  cdp->addStep(eqq, cr, {beq}, cargs);
  theory::Rewriter* rr = d_env.getRewriter();
  Node mergeq =
      rr->rewriteViaRule(ProofRewriteRule::QUANT_MERGE_PRENEX, umergeq);
  if (mergeq != eq[1])
  {
    Trace("brc-macro") << "Failed merge step" << std::endl;
    return false;
  }
  Node eqq2 = umergeq.eqNode(mergeq);
  cdp->addTheoryRewriteStep(eqq2, ProofRewriteRule::QUANT_MERGE_PRENEX);
  cdp->addStep(eq, ProofRule::TRANS, {eqq, eqq2}, {});
  Trace("brc-macro") << "Remains to prove: " << body1 << " == " << body2
                     << std::endl;
  // add the symmetry of the equality to the process vector, we will recursively
  // prove it via miniscoping steps below.
  Node eqqrs = body2.eqNode(body1);
  std::vector<Node> toProcess;
  std::unordered_set<Node> processed;
  toProcess.push_back(eqqrs);
  while (!toProcess.empty())
  {
    Node currEq = toProcess.back();
    toProcess.pop_back();
    if (processed.find(currEq) != processed.end())
    {
      continue;
    }
    processed.insert(currEq);
    if (currEq[0].getKind() != Kind::FORALL)
    {
      Trace("brc-macro") << "Unexpected subgoal" << std::endl;
      return false;
    }
    Kind bk = currEq[0][1].getKind();
    ProofRewriteRule prr =
        bk == Kind::ITE
            ? ProofRewriteRule::QUANT_MINISCOPE_ITE
            : (bk == Kind::OR ? ProofRewriteRule::QUANT_MINISCOPE_OR
                              : ProofRewriteRule::QUANT_MINISCOPE_AND);
    Node body2ms = rr->rewriteViaRule(prr, currEq[0]);
    Trace("brc-macro") << "Rewrite " << currEq[0] << " by " << prr
                       << " returns " << body2ms << std::endl;
    Node eqqm;
    if (body2ms.isNull())
    {
      // May have to remove unused variables. This is in rare cases where
      // we simultaneously prenex variables from different branches of an ITE.
      Node ceuv =
          rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, currEq[0]);
      if (!ceuv.isNull())
      {
        body2ms = rr->rewriteViaRule(prr, ceuv);
        Trace("brc-macro") << "Rewrite " << currEq[0] << " by " << prr
                           << " returns " << body2ms << std::endl;
      }
      if (body2ms.isNull())
      {
        Trace("brc-macro") << "Failed miniscope" << std::endl;
        return false;
      }
      Node eqce = currEq[0].eqNode(ceuv);
      cdp->addTheoryRewriteStep(eqce, ProofRewriteRule::QUANT_UNUSED_VARS);
      Node eqqm1 = ceuv.eqNode(body2ms);
      cdp->addTheoryRewriteStep(eqqm1, prr);
      eqqm = currEq[0].eqNode(body2ms);
      cdp->addStep(eqqm, ProofRule::TRANS, {eqce, eqqm1}, {});
    }
    else
    {
      eqqm = currEq[0].eqNode(body2ms);
      cdp->addTheoryRewriteStep(eqqm, prr);
    }
    if (body2ms != currEq[1])
    {
      if (body2ms.getKind() != currEq[1].getKind()
          || body2ms.getNumChildren() != currEq[1].getNumChildren())
      {
        Trace("brc-macro") << "Failed after miniscope" << std::endl;
        return false;
      }
      // We may have used alpha equivalence to rename variables, thus we
      // introduce a CONG step where children that are disequal are given as
      // subgoals.
      std::vector<Node> cpremises;
      for (size_t i = 0, nchildren = body2ms.getNumChildren(); i < nchildren;
           i++)
      {
        Node eqc = body2ms[i].eqNode(currEq[1][i]);
        cpremises.push_back(eqc);
        if (eqc[0] == eqc[1])
        {
          cdp->addStep(eqc, ProofRule::REFL, {}, {eqc[0]});
          continue;
        }
        if (eqc[1].getKind() == Kind::FORALL)
        {
          // just add subgoal, likely alpha equivalence
          cdp->addTrustedStep(eqc, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
          continue;
        }
        // maybe the result of QUANT_UNUSED_VARS?
        Node buv =
            rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, eqc[0]);
        if (buv == eqc[1])
        {
          cdp->addTheoryRewriteStep(eqc, ProofRewriteRule::QUANT_UNUSED_VARS);
          continue;
        }
        // otherwise recursely prove
        toProcess.push_back(eqc);
      }
      cargs.clear();
      cr = expr::getCongRule(body2ms, cargs);
      Node eqqb = body2ms.eqNode(currEq[1]);
      cdp->addStep(eqqb, cr, cpremises, cargs);
      cdp->addStep(currEq, ProofRule::TRANS, {eqqm, eqqb}, {});
    }
  }
  cdp->addStep(beq, ProofRule::SYMM, {eqqrs}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantPartitionConnectedFv(
    CDProof* cdp, const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand macro quant partition connected for " << eq
                     << std::endl;
  Node q = eq[0];
  Assert(q.getKind() == Kind::FORALL);
  Node origBody = q[1];
  std::unordered_set<Node> obvs(q[0].begin(), q[0].end());
  std::vector<Node> newBodyDisj;
  Assert(eq[1].getKind() == Kind::OR);
  std::vector<Node> newVars;
  for (const Node& d : eq[1])
  {
    if (d.getKind() == Kind::FORALL)
    {
      // Corner case: if a nested quantified formula, it may have no relation
      // to the original, in which case we treat it as a standalone literal.
      // We use hasSubterm to check for this.
      if (!expr::hasSubterm(origBody, d))
      {
        newBodyDisj.emplace_back(d[1]);
        for (const Node& v : d[0])
        {
          if (std::find(newVars.begin(), newVars.end(), v) == newVars.end())
          {
            newVars.emplace_back(v);
          }
          else
          {
            // variable was repeated
            DebugUnhandled();
            return false;
          }
        }
        continue;
      }
    }
    // handle the case where there are no variables from the original
    newBodyDisj.emplace_back(d);
  }
  std::vector<Node> transEq;
  // To prove (forall X F) = (forall X1 F1) or ... or (forall Xn Fn),
  // we first remove variables and reorder to ensure that X = X1 ... Xn.
  if (newVars.size() < q[0].getNumChildren())
  {
    theory::Rewriter* rr = d_env.getRewriter();
    Node uq = rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, q);
    if (uq.isNull())
    {
      return false;
    }
    Node eqqu = q.eqNode(uq);
    if (!cdp->addTheoryRewriteStep(eqqu, ProofRewriteRule::QUANT_UNUSED_VARS))
    {
      DebugUnhandled();
      return false;
    }
    transEq.emplace_back(eqqu);
    q = uq;
  }
  Node newVarList = nm->mkNode(Kind::BOUND_VAR_LIST, newVars);
  if (newVarList != q[0])
  {
    Node rq = nm->mkNode(Kind::FORALL, newVarList, q[1]);
    Node eqqr = q.eqNode(rq);
    if (!cdp->addStep(eqqr, ProofRule::QUANT_VAR_REORDERING, {}, {eqqr}))
    {
      DebugUnhandled();
      return false;
    }
    transEq.emplace_back(eqqr);
    q = rq;
  }
  Node newBody = nm->mkOr(newBodyDisj);
  Node eqb = origBody.eqNode(newBody);
  // We now prove
  //   (forall X F) = (forall X F1 or ... or Fn)
  if (!cdp->addStep(eqb, ProofRule::ACI_NORM, {}, {eqb}))
  {
    DebugUnhandled();
    return false;
  }
  Node newQuant = nm->mkNode(Kind::FORALL, q[0], newBody);
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(q, cargs);
  Node eqq = q.eqNode(newQuant);
  cdp->addStep(eqq, cr, {eqb}, cargs);
  transEq.emplace_back(eqq);
  Node eqq2 = newQuant.eqNode(eq[1]);
  // Then prove
  //   (forall X F1 or ... or Fn) = (forall X1 F1) or ... or (forall Xn Fn)
  // via ProofRewriteRule::QUANT_MINISCOPE_OR.
  if (!cdp->addTheoryRewriteStep(eqq2, ProofRewriteRule::QUANT_MINISCOPE_OR))
  {
    DebugUnhandled();
    return false;
  }
  transEq.emplace_back(eqq2);
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantVarElimEq(CDProof* cdp,
                                                       const Node& eq)
{
  Node q = eq[0];
  Assert(q.getKind() == Kind::FORALL);
  std::vector<Node> args(q[0].begin(), q[0].end());
  std::vector<Node> vars;
  std::vector<Node> subs;
  std::vector<Node> lits;
  theory::quantifiers::QuantifiersRewriter qrew(
      nodeManager(), d_env.getRewriter(), options());
  if (!qrew.getVarElim(q[1], args, vars, subs, lits, cdp))
  {
    // if we fail here, the variable elimination may have corresponded
    // to one where proofs cannot be replayed, e.g. if varElimEntEq is true.
    return false;
  }
  if (args.size() != q[0].getNumChildren() - 1)
  {
    // should have eliminated exactly one variable
    DebugUnhandled();
    return false;
  }
  Assert(vars.size() == 1);
  Trace("brc-macro") << "Ensure quant var elim eq: " << eq << std::endl;
  Trace("brc-macro") << "Eliminate " << vars << " -> " << subs << " from "
                     << lits << std::endl;
  // From call to getVarElim, we have a proof of lits[0] = (vars[0] = subs[0]).
  // merge prenex in reverse to handle the other irrelevant variables first
  NodeManager* nm = nodeManager();
  Node body1;
  Node body2;
  if (eq[1].getKind() == Kind::FORALL)
  {
    body1 = nm->mkNode(
        Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, vars[0]), q[1]);
    std::vector<Node> transEq;
    Node unmergeQ = nm->mkNode(Kind::FORALL, eq[1][0], body1);
    Node mergeQ;
    Node q0v = q[0];
    if (vars[0] != q0v[q0v.getNumChildren() - 1])
    {
      // use reordering if the eliminated variable is not the last one
      std::vector<Node> mvars(eq[1][0].begin(), eq[1][0].end());
      mvars.push_back(vars[0]);
      mergeQ = nm->mkNode(
          Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, mvars), q[1]);
      Node eqq = q.eqNode(mergeQ);
      cdp->addStep(eqq, ProofRule::QUANT_VAR_REORDERING, {}, {eqq});
      transEq.push_back(eqq);
    }
    else
    {
      mergeQ = q;
    }
    Node eqq2s = unmergeQ.eqNode(mergeQ);
    cdp->addTheoryRewriteStep(eqq2s, ProofRewriteRule::QUANT_MERGE_PRENEX);
    Node eqq2 = mergeQ.eqNode(unmergeQ);
    cdp->addStep(eqq2, ProofRule::SYMM, {eqq2s}, {});
    transEq.push_back(eqq2);
    body2 = eq[1][1];
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(unmergeQ, cargs);
    Node beq = body1.eqNode(body2);
    Node eqq3 = unmergeQ.eqNode(eq[1]);
    cdp->addStep(eqq3, cr, {beq}, cargs);
    transEq.push_back(eqq3);
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  }
  else
  {
    body1 = eq[0];
    body2 = eq[1];
  }
  // we now have proven forall Y1 x Y2. F = forall Y1 Y2. F *sigma is a
  // consequence of forall x. F = F * sigma, now prove the latter equality.
  Trace("brc-macro") << "Remains to prove: " << body1 << " == " << body2
                     << std::endl;
  Assert(body1.getKind() == Kind::FORALL);
  Node eqLit = vars[0].eqNode(subs[0]).notNode();
  Node lit = lits[0].negate();
  // add a copy of the equality literal and prove it is redundant with ACI_NORM
  std::vector<Node> disj;
  disj.push_back(lit);
  if (body1[1].getKind() == Kind::OR)
  {
    disj.insert(disj.end(), body1[1].begin(), body1[1].end());
  }
  else
  {
    disj.push_back(body1[1]);
  }
  Node body1r = nm->mkOr(disj);
  disj[0] = eqLit;
  Node body1re = nm->mkOr(disj);
  std::vector<Node> transEqBody;
  Node eqBody = body1[1].eqNode(body1r);
  cdp->addStep(eqBody, ProofRule::ACI_NORM, {}, {eqBody});
  transEqBody.push_back(eqBody);
  if (eqLit != lit)
  {
    Node litdn = lits[0].notNode();
    // prove congruence over NOT
    Node litEquiv = litdn[0].eqNode(eqLit[0]);
    Trace("brc-macro") << "prove congruence on NOT" << std::endl;
    proveCong(cdp, litdn, {litEquiv});
    litEquiv = litdn.eqNode(eqLit);
    // handle double negation
    if (litdn != lit)
    {
      Node eqdn = lit.eqNode(litdn);
      cdp->addTrustedStep(
          eqdn, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      Node litEquiv2 = lit.eqNode(eqLit);
      cdp->addStep(litEquiv2, ProofRule::TRANS, {eqdn, litEquiv}, {});
      litEquiv = litEquiv2;
    }
    Trace("brc-macro") << "prove congruence on OR" << std::endl;
    // prove congruence over OR
    proveCong(cdp, body1r, {litEquiv});
    Node eqbr = body1r.eqNode(body1re);
    transEqBody.emplace_back(eqbr);
    eqBody = body1[1].eqNode(body1re);
  }
  if (transEqBody.size() > 1)
  {
    cdp->addStep(eqBody, ProofRule::TRANS, transEqBody, {});
  }
  // We've now proven that (or (not (= x t)) F) is equivalent to F, we can
  // forall x. F =
  // forall x. (or (not (= x t)) F) =
  // F * { x -> t }
  // where the latter equality is proven by QUANT_VAR_ELIM_EQ.
  std::vector<Node> finalTransEq;
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(body1, cargs);
  Node body1p = nm->mkNode(Kind::FORALL, body1[0], body1re);
  Node eqq = body1.eqNode(body1p);
  cdp->addStep(eqq, cr, {eqBody}, cargs);
  finalTransEq.push_back(eqq);
  eqq = body1p.eqNode(body2);
  if (!doTheoryRewrite(cdp, eqq, ProofRewriteRule::QUANT_VAR_ELIM_EQ))
  {
    return false;
  }
  finalTransEq.push_back(eqq);
  Node beq = body1.eqNode(body2);
  cdp->addStep(beq, ProofRule::TRANS, finalTransEq, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroDtVarExpand(CDProof* cdp,
                                                    const Node& eq)
{
  Trace("brc-macro") << "Expand macro dt var expand " << eq << std::endl;
  // just need to find the index
  size_t index;
  Node qn = theory::quantifiers::QuantifiersRewriter::computeDtVarExpand(
      nodeManager(), eq[0], index);
  if (qn == eq[1])
  {
    // use the utility to get the proof
    std::shared_ptr<ProofNode> pfn =
        theory::quantifiers::QuantDSplit::getQuantDtSplitProof(
            d_env, eq[0], index);
    Assert(pfn->getResult() == eq);
    cdp->addProof(pfn);
    return true;
  }
  return false;
}

bool BasicRewriteRCons::ensureProofMacroQuantMiniscope(CDProof* cdp,
                                                       const Node& eq)
{
  Trace("brc-macro") << "Expand quant miniscope " << eq[0] << " == " << eq[1]
                     << std::endl;
  Node q = eq[0];
  Assert(q.getKind() == Kind::FORALL);
  NodeManager* nm = nodeManager();
  Kind bk = q[1].getKind();
  Assert(bk == Kind::AND || bk == Kind::ITE);
  ProofRewriteRule prr = bk == Kind::AND
                             ? ProofRewriteRule::QUANT_MINISCOPE_AND
                             : ProofRewriteRule::QUANT_MINISCOPE_ITE;
  theory::Rewriter* rr = d_env.getRewriter();
  Node mq = rr->rewriteViaRule(prr, q);
  Node equiv = q.eqNode(mq);
  cdp->addTheoryRewriteStep(equiv, prr);
  if (mq == eq[1])
  {
    return true;
  }
  if (mq.getNumChildren() != eq[1].getNumChildren())
  {
    DebugUnhandled() << "Unexpected input ensureProofMacroQuantMiniscope "
                     << eq;
    return false;
  }
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node equiv2 = mq.eqNode(eq[1]);
  std::vector<Node> premises;
  // each conjunct is either equal to the corresponding conjunct, the
  // result of dropping all variables from the corresponding conjunct, or
  // is alpha equivalent to the corresponding conjunct.
  for (size_t i = 0, nconj = mq.getNumChildren(); i < nconj; i++)
  {
    Node eqc = mq[i].eqNode(eq[1][i]);
    premises.emplace_back(eqc);
    if (mq[i] == eq[1][i])
    {
      cdp->addStep(eqc, ProofRule::REFL, {}, {mq[i]});
      continue;
    }
    Assert(mq[i].getKind() == Kind::FORALL);
    if (mq[i][1] == eq[1][i])
    {
      Node mqc = rr->rewriteViaRule(ProofRewriteRule::QUANT_UNUSED_VARS, mq[i]);
      if (mqc == eq[1][i])
      {
        cdp->addTheoryRewriteStep(eqc, ProofRewriteRule::QUANT_UNUSED_VARS);
        continue;
      }
    }
    else if (eq[1][i].getKind() == Kind::FORALL)
    {
      std::vector<Node> v1(mq[i][0].begin(), mq[i][0].end());
      std::vector<Node> v2(eq[1][i][0].begin(), eq[1][i][0].end());
      std::vector<Node> aeArgs;
      aeArgs.push_back(mq[i]);
      aeArgs.push_back(nm->mkNode(Kind::SEXPR, v1));
      aeArgs.push_back(nm->mkNode(Kind::SEXPR, v2));
      Node res = pc->checkDebug(ProofRule::ALPHA_EQUIV, {}, aeArgs);
      if (!res.isNull() && res[1] == eq[1][i])
      {
        cdp->addStep(res, ProofRule::ALPHA_EQUIV, {}, aeArgs);
        continue;
      }
    }
    DebugUnhandled() << "Failed ensureProofMacroQuantMiniscope " << eq;
    return false;
  }
  // add the CONG step to conclude AND or ITE terms are equal
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(mq, cargs);
  cdp->addStep(equiv2, cr, premises, cargs);
  // transitive
  cdp->addStep(eq, ProofRule::TRANS, {equiv, equiv2}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantRewriteBody(CDProof* cdp,
                                                         const Node& eq)
{
  Trace("brc-macro") << "Expand quant rewrite body " << eq[0] << " == " << eq[1]
                     << std::endl;
  // Call the utility again with proof tracking and construct the term
  // conversion proof. This proof itself may have trust steps in it.
  // We ensure the proof generator does not rewrite in the pattern list using a
  // term context.
  WithinKindTermContext wktc(Kind::INST_PATTERN_LIST);
  TConvProofGenerator tcpg(d_env,
                           nullptr,
                           TConvPolicy::ONCE,
                           TConvCachePolicy::NEVER,
                           "EnsureProofMacroQuantRewrite",
                           &wktc);
  theory::quantifiers::QuantifiersRewriter qrew(
      nodeManager(), d_env.getRewriter(), options());
  Node qr = qrew.computeRewriteBody(eq[0], &tcpg);
  if (qr != eq[1])
  {
    DebugUnhandled() << "Failed to rewrite " << eq[0] << " to " << qr
                     << " != " << eq[1];
    return false;
  }
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(eq);
  cdp->addProof(pfn);
  return true;
}

bool BasicRewriteRCons::ensureProofMacroBvEqSolve(CDProof* cdp, const Node& eq)
{
  Trace("brc-macro") << "Expand bv eq solve " << eq[0] << " == " << eq[1]
                     << std::endl;
  Node ns = nodeManager()->mkNode(Kind::BITVECTOR_SUB, eq[0][0], eq[0][1]);
  Node nsn = theory::arith::PolyNorm::getPolyNorm(ns);
  Node zero = theory::bv::utils::mkZero(nodeManager(),
                                        nsn.getType().getBitVectorSize());
  Node eqn = nsn.eqNode(zero);
  Node equiv = eq[0].eqNode(eqn);
  if (!ensureProofArithPolyNormRel(cdp, equiv))
  {
    Trace("brc-macro") << "...fail arith poly norm rel" << std::endl;
    return false;
  }
  Node equiv2 = eqn.eqNode(eq[1]);
  if (!cdp->addStep(equiv2, ProofRule::EVALUATE, {}, {eqn}))
  {
    Trace("brc-macro") << "...fail evaluate" << std::endl;
    return false;
  }
  cdp->addStep(eq, ProofRule::TRANS, {equiv, equiv2}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroElimShadow(CDProof* cdp, const Node& eq)

{
  Trace("brc-macro") << "Expand macro eliminate shadow for " << eq << std::endl;
  // Get equalities between subterms that are disequal in LHS/RHS. These will
  // be added as rewrite steps below.
  std::vector<Node> matchConds;
  expr::getConversionConditions(eq[0], eq[1], matchConds, true);
  // use conversion proof, must rewrite ops
  TConvProofGenerator tcpg(d_env,
                           nullptr,
                           TConvPolicy::ONCE,
                           TConvCachePolicy::NEVER,
                           "MacroLambdaAppElimShadow",
                           nullptr,
                           true);
  for (const Node& mc : matchConds)
  {
    Trace("brc-macro") << "- subgoal " << mc << std::endl;
    // the step should be shown by alpha-equivalance
    tcpg.addRewriteStep(mc[0],
                        mc[1],
                        nullptr,
                        true,
                        TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
  }
  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
  Node res = pfn->getResult();
  if (res[1] == eq[1])
  {
    cdp->addProof(pfn);
    return true;
  }
  DebugUnhandled();
  return false;
}

bool BasicRewriteRCons::ensureProofMacroArraysNormalizeOp(CDProof* cdp,
                                                          const Node& eq)
{
  Trace("brc-macro") << "Expand arrays normalize op " << eq << std::endl;
  TConvProofGenerator tcpg(d_env, nullptr, TConvPolicy::FIXPOINT);
  theory::arrays::TheoryArraysRewriter arew(nodeManager(), d_env.getRewriter());
  Node nr = arew.computeNormalizeOp(eq[0], &tcpg);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
  if (pfn->getResult() == eq)
  {
    Trace("brc-macro") << "...proof is " << *pfn.get() << std::endl;
    cdp->addProof(pfn);
    return true;
  }
  Trace("brc-macro") << "...failed, got " << pfn->getResult()[1] << std::endl;
  DebugUnhandled();
  return false;
}

bool BasicRewriteRCons::ensureProofArithPolyNormRel(CDProof* cdp,
                                                    const Node& eq)
{
  Trace("brc-macro") << "Ensure arith poly norm rel: " << eq << std::endl;
  Rational rx, ry;
  if (!theory::arith::PolyNorm::isArithPolyNormRel(eq[0], eq[1], rx, ry))
  {
    Trace("brc-macro") << "...fail rule" << std::endl;
    return false;
  }
  Node premise =
      theory::arith::PolyNorm::getArithPolyNormRelPremise(eq[0], eq[1], rx, ry);
  Trace("brc-macro") << "Show " << premise << " by arith poly norm"
                     << std::endl;
  bool isBv = eq[0][0].getType().isBitVector();
  ProofRule rule = isBv ? ProofRule::BV_POLY_NORM : ProofRule::ARITH_POLY_NORM;
  if (!cdp->addStep(premise, rule, {}, {premise}))
  {
    Trace("brc-macro") << "...fail premise" << std::endl;
    return false;
  }
  ProofRule rrule =
      isBv ? ProofRule::BV_POLY_NORM_EQ : ProofRule::ARITH_POLY_NORM_REL;
  if (!cdp->addStep(eq, rrule, {premise}, {eq}))
  {
    Trace("brc-macro") << "...fail application" << std::endl;
    return false;
  }
  return true;
}

Node BasicRewriteRCons::proveSymm(CDProof* cdp, const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Node eqs = eq[1].eqNode(eq[0]);
  cdp->addStep(eqs, ProofRule::SYMM, {eq}, {});
  return eqs;
}

Node BasicRewriteRCons::proveCong(CDProof* cdp,
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

Node BasicRewriteRCons::proveDualImplication(CDProof* cdp,
                                             const Node& impl,
                                             const Node& implrev)
{
  Assert(impl.getKind() == Kind::IMPLIES && implrev.getKind() == Kind::IMPLIES
         && impl[0] == implrev[1] && impl[1] == implrev[0]);
  NodeManager* nm = nodeManager();
  Node dualImpl = nm->mkNode(Kind::AND, impl, implrev);
  cdp->addStep(dualImpl, ProofRule::AND_INTRO, {impl, implrev}, {});
  Node eqfinal = impl[0].eqNode(impl[1]);
  Node dualImplEq = nm->mkNode(Kind::EQUAL, dualImpl, eqfinal);
  Trace("brc-macro") << "- dual implication subgoal " << dualImplEq
                     << std::endl;
  cdp->addTrustedStep(dualImplEq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdp->addStep(eqfinal, ProofRule::EQ_RESOLVE, {dualImpl, dualImplEq}, {});
  return eqfinal;
}

bool BasicRewriteRCons::tryTheoryRewrite(CDProof* cdp,
                                         const Node& eq,
                                         theory::TheoryRewriteCtx ctx)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("trewrite-rcons") << "Find rule " << eq << std::endl;
  ProofRewriteRule prid = d_env.getRewriter()->findRule(eq[0], eq[1], ctx);
  if (prid != ProofRewriteRule::NONE)
  {
    // Do not add the step in the call to tryStep, instead we add it via
    // ensureProofForTheoryRewrite.
    if (tryRule(cdp,
                eq,
                ProofRule::THEORY_REWRITE,
                {mkRewriteRuleNode(nodeManager(), prid), eq},
                false))
    {
      Trace("trewrite-rcons") << "...got " << prid << std::endl;
      // Theory rewrites may require macro expansion
      ensureProofForTheoryRewrite(cdp, prid, eq);
      return true;
    }
  }
  return false;
}

bool BasicRewriteRCons::doTheoryRewrite(CDProof* cdp,
                                        const Node& eq,
                                        ProofRewriteRule r)
{
  Node er = d_env.getRewriter()->rewriteViaRule(r, eq[0]);
  if (er == eq[1])
  {
    cdp->addTheoryRewriteStep(eq, r);
    return true;
  }
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal

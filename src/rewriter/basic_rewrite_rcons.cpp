/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "theory/arith/arith_msum.h"
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
#include "theory/strings/arith_entail.h"
#include "theory/strings/regexp_entail.h"
#include "theory/strings/sequences_rewriter.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
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
      d_bvRewElab(env)
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

bool BasicRewriteRCons::postProve(
    CDProof* cdp,
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
      if (ensureProofMacroArithStringPredEntail(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION:
      if (ensureProofMacroReInterUnionInclusion(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH:
      if (ensureProofMacroSubstrStripSymLength(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX:
      if (ensureProofMacroStrEqLenUnifyPrefix(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY:
      if (ensureProofMacroStrEqLenUnify(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS:
    case ProofRewriteRule::MACRO_STR_SPLIT_CTN:
      if (ensureProofMacroOverlap(id, cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_COMPONENT_CTN:
      if (ensureProofMacroStrComponentCtn(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT:
      if (ensureProofMacroStrConstNCtnConcat(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION:
      if (ensureProofMacroStrInReInclusion(cdp, eq))
      {
        handledMacro = true;
      }
      break;
    case ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM:
      if (ensureProofMacroReInterUnionConstElim(cdp, eq))
      {
        handledMacro = true;
      }
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
    case ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ:
      if (ensureProofMacroQuantVarElimIneq(cdp, eq))
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
      if (ensureProofMacroLambdaCaptureAvoid(cdp, eq))
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

bool BasicRewriteRCons::ensureProofMacroBoolBvInvertSolve(CDProof* cdp,
                                                          const Node& eq)
{
  Trace("brc-macro") << "Expand Bool BV invert solve " << eq[0]
                     << " == " << eq[1] << std::endl;
  Assert(eq[0].getKind() == Kind::EQUAL);
  Assert(eq[0][0].getKind() == Kind::EQUAL
         && eq[0][1].getKind() == Kind::EQUAL);
  std::unordered_set<Kind> disallowedKinds;
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
                          nm->mkNode(Kind::TO_REAL, rewRel[0]),
                          nm->mkNode(Kind::TO_REAL, rewRel[1]));
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
  Node rew = nm->mkNode(rk, nm->mkNode(Kind::TO_REAL, p.first), p.second);
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
    Node cceil = nm->mkConstInt(p.second.getConst<Rational>().ceiling());
    tgt = nm->mkNode(rk, p.first, cceil);
  }
  // the last step can be shown by the RARE rules
  // arith-int-eq-conflict or arith-int-geq-tighten
  eqq = rew.eqNode(tgt);
  cdp->addTrustedStep(eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  transEq.push_back(eqq);
  if (tgt != eq[1])
  {
    eqq = tgt.eqNode(eq[1]);
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
    Assert(false) << "Failed to show " << rhs << " == " << eq[1] << std::endl;
    return false;
  }
  // use ACI_NORM
  cdp->addProof(pfn);
  Node eqa = rhs.eqNode(eq[1]);
  cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa});
  cdp->addStep(eq, ProofRule::TRANS, {res, eqa}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroArithStringPredEntail(CDProof* cdp,
                                                              const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("brc-macro") << "Expand entailment for " << eq << std::endl;
  theory::strings::ArithEntail ae(nodeManager(), nullptr);
  Node lhs = eq[0];
  Node eqi = eq;
  // First normalize LT/GT/LEQ to GEQ.
  if (lhs.getKind() != Kind::EQUAL && lhs.getKind() != Kind::GEQ)
  {
    Node lhsn = ae.normalizeGeq(lhs);
    Node eqLhs = lhs.eqNode(lhsn);
    cdp->addTrustedStep(
        eqLhs, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    eqi = lhsn.eqNode(eq[1]);
    cdp->addStep(eq, ProofRule::TRANS, {eqLhs, eqi}, {});
    Trace("brc-macro") << "- GEQ normalize is " << eqi << std::endl;
  }
  // Then do basic length intro, which rewrites (str.len (str.++ x y))
  // to (+ (str.len x) (str.len y)).
  TConvProofGenerator tcpg(d_env, nullptr);
  Node eqii = ae.rewriteLengthIntro(eqi, &tcpg);
  if (eqii != eqi)
  {
    Node equiv = eqi.eqNode(eqii);
    std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(equiv);
    cdp->addProof(pfn);
    Node equivs = eqii.eqNode(eqi);
    cdp->addStep(equivs, ProofRule::SYMM, {equiv}, {});
    cdp->addStep(eqi, ProofRule::EQ_RESOLVE, {eqii, equivs}, {});
    Trace("brc-macro") << "- length intro is " << eqii << std::endl;
    // now, must prove eqii
  }
  lhs = eqii[0];
  Node exp;
  Node ret = ae.rewritePredViaEntailment(lhs, exp, true);
  Assert(ret == eqii[1]);
  Trace("brc-macro") << "- explanation is " << exp << std::endl;
  // if trivially true equality
  if (exp.isNull())
  {
    // explanation true if we are an equality that is trivially true
    Assert(eqii[0].getKind() == Kind::EQUAL);
    if (eqii[0][0] == eqii[0][1])
    {
      cdp->addStep(eqii[0], ProofRule::REFL, {}, {eqii[0][0]});
    }
    else
    {
      Assert(theory::arith::PolyNorm::isArithPolyNorm(eqii[0][0], eqii[0][1]));
      // prove via ARITH_POLY_NORM.
      cdp->addStep(eqii[0], ProofRule::ARITH_POLY_NORM, {}, {eqii[0]});
    }
    cdp->addStep(eqii, ProofRule::TRUE_INTRO, {eqii[0]}, {});
    return true;
  }
  Node expRew = ae.rewriteArith(exp);
  Node zero = nodeManager()->mkConstInt(Rational(0));
  Node geq = nodeManager()->mkNode(Kind::GEQ, expRew, zero);
  Trace("brc-macro") << "- rewritten predicate is " << geq << std::endl;
  Node approx = ae.findApprox(expRew, true);
  if (approx.isNull())
  {
    Trace("brc-macro") << "...failed to find approximation" << std::endl;
    Assert(false);
    return false;
  }
  Node truen = nodeManager()->mkConst(true);
  Node approxRew = ae.rewriteArith(approx);
  Node approxGeq = nodeManager()->mkNode(Kind::GEQ, approx, zero);
  Node approxRewGeq = nodeManager()->mkNode(Kind::GEQ, approxRew, zero);
  Trace("brc-macro") << "- approximation predicate is " << approxGeq
                     << std::endl;
  std::vector<Node> transEq;
  if (expRew != approx)
  {
    Node aeq = geq.eqNode(approxGeq);
    // (>= expRew 0) = (>= approx 0)
    Trace("brc-macro") << "- prove " << aeq << " via pred-safe-approx"
                       << std::endl;
    cdp->addTheoryRewriteStep(aeq,
                              ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX);
    transEq.push_back(aeq);
  }
  if (approx != approxRew)
  {
    Node areq = approxGeq.eqNode(approxRewGeq);
    Trace("brc-macro") << "- prove " << areq << " via arith-poly-norm"
                       << std::endl;
    if (!ensureProofArithPolyNormRel(cdp, areq))
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      Assert(false);
      return false;
    }
    transEq.push_back(areq);
  }
  // (>= approx 0) = true
  Node teq = approxRewGeq.eqNode(truen);
  // do not use rewriter in evaluate
  Node ev = evaluate(approxRewGeq, {}, {}, false);
  if (ev == truen)
  {
    Trace("brc-macro") << "- prove " << teq << " via evaluate" << std::endl;
    cdp->addStep(teq, ProofRule::EVALUATE, {}, {approxRewGeq});
  }
  else
  {
    Trace("brc-macro") << "- prove " << teq << " via pred-entail" << std::endl;
    cdp->addTheoryRewriteStep(teq, ProofRewriteRule::ARITH_STRING_PRED_ENTAIL);
  }
  transEq.push_back(teq);
  // put the above three steps together with TRANS
  if (transEq.size() > 1)
  {
    teq = geq.eqNode(truen);
    cdp->addStep(teq, ProofRule::TRANS, transEq, {});
  }

  // now have (>= expRew 0) = true, stored in teq

  if (lhs == expRew)
  {
    Trace("brc-macro") << "...success (no normalization)" << std::endl;
    return true;
  }
  if (!ret.getConst<bool>())
  {
    Trace("brc-macro") << "- false case, setting up conflict" << std::endl;
    cdp->addStep(geq, ProofRule::TRUE_ELIM, {teq}, {});
    Assert(exp.getKind() == Kind::SUB);
    Node posTerm = exp[0].getKind() == Kind::SUB ? exp[0][0] : exp[0];
    Assert(posTerm == lhs[0] || posTerm == lhs[1]);
    bool isLhs = posTerm == lhs[0];
    Trace("brc-macro") << "- isLhs is " << isLhs << std::endl;
    std::vector<Node> children;
    children.push_back(geq);
    children.push_back(lhs);
    std::vector<Node> args;
    // Must flip signs to ensure it is <=, as required by
    // MACRO_ARITH_SCALE_SUM_UB. This rule sums inequalities based on the
    // coefficients in args.
    args.push_back(nodeManager()->mkConstInt(Rational(-1)));
    args.push_back(nodeManager()->mkConstInt(Rational(isLhs ? 1 : -1)));
    Trace("brc-macro") << "- compute sum bound for " << children << " " << args
                       << std::endl;
    Node sumBound =
        theory::arith::expandMacroSumUb(nodeManager(), children, args, cdp);
    Trace("brc-macro") << "- sum bound is " << sumBound << std::endl;
    if (sumBound.isNull())
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      Assert(false);
      return false;
    }
    Assert(sumBound.getNumChildren() == 2);
    Node py = nodeManager()->mkNode(Kind::SUB, sumBound[0], sumBound[1]);
    theory::arith::PolyNorm pn = theory::arith::PolyNorm::mkPolyNorm(py);
    Rational pyr;
    if (!pn.isConstant(pyr))
    {
      Trace("brc-macro") << "...failed to prove constant after normalization"
                         << std::endl;
      Assert(false);
      return false;
    }
    Node cpred = nodeManager()->mkNode(
        sumBound.getKind(), nodeManager()->mkConstInt(pyr), zero);
    Node peq = sumBound.eqNode(cpred);
    if (!ensureProofArithPolyNormRel(cdp, peq))
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      Assert(false);
      return false;
    }
    Node cceq = cpred.eqNode(ret);
    cdp->addStep(cceq, ProofRule::EVALUATE, {}, {cpred});
    Node sumEqFalse = sumBound.eqNode(ret);
    cdp->addStep(sumEqFalse, ProofRule::TRANS, {peq, cceq}, {});
    Node notSum = sumBound.notNode();
    cdp->addStep(notSum, ProofRule::FALSE_ELIM, {sumEqFalse}, {});
    cdp->addStep(ret, ProofRule::CONTRA, {sumBound, notSum}, {});
    Node notLhs = lhs.notNode();
    cdp->addStep(notLhs, ProofRule::SCOPE, {ret}, {lhs});
    cdp->addStep(eqii, ProofRule::FALSE_INTRO, {notLhs}, {});
  }
  else
  {
    Trace("brc-macro") << "- true case, prove equal" << std::endl;
    Assert(lhs.getKind() == Kind::GEQ);
    // should be able to show equivalence by polynomial normalization
    Node peq = lhs.eqNode(geq);
    if (!ensureProofArithPolyNormRel(cdp, peq))
    {
      Trace("brc-macro") << "...failed to show normalization (true case) "
                         << lhs << " and " << geq << std::endl;
      Assert(false);
      return false;
    }
    cdp->addStep(eqii, ProofRule::TRANS, {peq, teq}, {});
  }
  Trace("brc-macro") << "...success" << std::endl;
  return true;
}

bool BasicRewriteRCons::ensureProofMacroReInterUnionInclusion(CDProof* cdp,
                                                              const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand re inter union inclusion " << eq << std::endl;
  // partition eq[0] in the portion responsible for the rewrite which was
  // removed from eq[1] (diff) and the remainder (rem).
  std::vector<Node> diff;
  std::vector<Node> rem;
  Kind k = eq[0].getKind();
  if (k == eq[1].getKind())
  {
    size_t i1 = 1;
    for (size_t i = 0, nchild = eq[0].getNumChildren(); i < nchild; i++)
    {
      if (i1 >= eq[1].getNumChildren() || eq[0][i] != eq[1][i1])
      {
        diff.push_back(eq[0][i]);
      }
      else
      {
        i1++;
      }
    }
    // ignore the first child
    rem.insert(rem.end(), eq[1].begin() + 1, eq[1].end());
  }
  else
  {
    diff.insert(diff.end(), eq[0].begin(), eq[0].end());
  }
  // should have found 2 regular expressions in the difference
  if (diff.size() != 2)
  {
    Trace("brc-macro") << "...fail diff " << diff << std::endl;
    Assert(false);
    return false;
  }
  // reorient so complement is second
  if (diff[0].getKind() == Kind::REGEXP_COMPLEMENT)
  {
    Node tmp = diff[0];
    diff[0] = diff[1];
    diff[1] = tmp;
  }
  Node d = nm->mkNode(k, diff);
  Trace("brc-macro") << "...input difference " << d << std::endl;
  // use simpler form of rule on diff.
  ProofRewriteRule rule = k == Kind::REGEXP_INTER
                              ? ProofRewriteRule::RE_INTER_INCLUSION
                              : ProofRewriteRule::RE_UNION_INCLUSION;
  theory::Rewriter* rr = d_env.getRewriter();
  Node ret = rr->rewriteViaRule(rule, d);
  if (ret.isNull() || (ret != eq[1] && ret != eq[1][0]))
  {
    Trace("brc-macro") << "...fail target " << ret << std::endl;
    Assert(false);
    return false;
  }
  Node equiv = d.eqNode(ret);
  Trace("brc-macro") << "... successfully proven " << equiv << std::endl;
  cdp->addTheoryRewriteStep(equiv, rule);
  // prove we can group eq[0] into (<op> diff rem).
  Node r = d;
  if (!rem.empty())
  {
    Node remr = rem.size() == 1 ? rem[0] : nm->mkNode(k, rem);
    r = nm->mkNode(k, d, remr);
  }
  std::vector<Node> transEq;
  if (eq[0] != r)
  {
    Node eqa = eq[0].eqNode(r);
    if (!cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa}))
    {
      Trace("brc-macro") << "...fail aci norm " << eqa << std::endl;
      Assert(false);
      return false;
    }
    Trace("brc-macro") << "...aci norm " << eqa << std::endl;
    transEq.push_back(eqa);
  }
  // finally, prove that the result of (<op> diff' rem) is eq[1], where
  // diff' is the result of applying rule.
  if (rem.empty())
  {
    transEq.push_back(equiv);
  }
  else
  {
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(r, cargs);
    Node refl = r[1].eqNode(r[1]);
    cdp->addStep(refl, ProofRule::REFL, {}, {r[1]});
    Node rret = r.eqNode(nm->mkNode(k, ret, r[1]));
    cdp->addStep(rret, cr, {equiv, refl}, cargs);
    transEq.push_back(rret);
    // should be proven by RARE rewrite
    Node eqt = rret.eqNode(eq[1]);
    Trace("brc-macro") << "... subgoal " << eqt << std::endl;
    cdp->addTrustedStep(eqt, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  }
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroReInterUnionConstElim(CDProof* cdp,
                                                              const Node& eq)
{
  Trace("brc-macro") << "Expand macro re inter union const elim for " << eq
                     << std::endl;
  if (eq[0].getKind() == Kind::REGEXP_INTER)
  {
    // RARE should suffice to show the intersection case
    // via rules re-inter-cstring or re-inter-cstring-neg
    // Note these may require calling membership evaluation as a subcall,
    // so we mark this non-simple.
    cdp->addTrustedStep(eq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    return true;
  }
  Assert(eq[0].getKind() == Kind::REGEXP_UNION);
  std::vector<Node> ch1(eq[0].begin(), eq[0].end());
  std::vector<Node> ch2;
  if (eq[1].getKind() == Kind::REGEXP_UNION)
  {
    ch2.insert(ch2.end(), eq[1].begin(), eq[1].end());
  }
  else
  {
    ch2.push_back(eq[1]);
  }
  std::vector<Node> diff;
  size_t i2 = 0;
  for (size_t i1 = 0, nchild = ch1.size(); i1 < nchild; i1++)
  {
    if (i2 < ch2.size() && ch1[i1] == ch2[i2])
    {
      i2++;
    }
    else
    {
      diff.push_back(ch1[i1]);
    }
  }
  Node curr = eq[1];
  std::vector<Node> transEq;
  NodeManager* nm = nodeManager();
  for (size_t i = 0, ndiff = diff.size(); i < ndiff; i++)
  {
    size_t ii = (ndiff - i - 1);
    Node next = nm->mkNode(Kind::REGEXP_UNION, diff[ii], curr);
    Node eqc = next.eqNode(curr);
    // RARE rule re-union-const-elim should suffice
    // Note these may require calling membership evaluation as a subcall,
    // so we mark this non-simple
    cdp->addTrustedStep(eqc, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    transEq.push_back(eqc);
    curr = next;
  }
  if (eq[0] != curr)
  {
    Node eqa = eq[0].eqNode(curr);
    if (!cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa}))
    {
      Assert(false);
      return false;
    }
    transEq.push_back(eqa);
  }
  if (transEq.size() > 1)
  {
    std::reverse(transEq.begin(), transEq.end());
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  }
  return true;
}

bool BasicRewriteRCons::ensureProofMacroSubstrStripSymLength(CDProof* cdp,
                                                             const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand substring strip for " << eq << std::endl;
  Assert(eq.getKind() == Kind::EQUAL);
  Node lhs = eq[0];
  Assert(lhs.getKind() == Kind::STRING_SUBSTR);
  theory::strings::Rewrite rule;
  // call the same utility that proved it
  theory::strings::ArithEntail ae(nm, nullptr);
  theory::strings::StringsEntail sent(nullptr, ae);
  std::vector<Node> ch1;
  std::vector<Node> ch2;
  Node rhs = sent.rewriteViaMacroSubstrStripSymLength(lhs, rule, ch1, ch2);
  Trace("brc-macro") << "...was via string rewrite rule " << rule << std::endl;
  Assert(rhs == eq[1]);
  TypeNode stype = lhs.getType();
  Node cm1 = theory::strings::utils::mkConcat(ch1, stype);
  Node cm2 = theory::strings::utils::mkConcat(ch2, stype);
  Node cm;
  // depending on the rule, are either stripping from front or back
  if (rule == theory::strings::Rewrite::SS_STRIP_END_PT)
  {
    cm = nm->mkNode(Kind::STRING_CONCAT, cm1, cm2);
  }
  else
  {
    cm = nm->mkNode(Kind::STRING_CONCAT, cm2, cm1);
  }
  if (cm == lhs[0])
  {
    return false;
  }
  Node eq1 = nm->mkNode(Kind::EQUAL, lhs[0], cm);
  // It is likely provable by ACI_NORM. However, if it involves splitting
  // word constants, we require going through the rewrite term converter.
  if (expr::isACINorm(lhs[0], cm))
  {
    cdp->addStep(eq1, ProofRule::ACI_NORM, {}, {eq1});
    Trace("brc-macro") << "- via ACI_NORM " << eq1 << std::endl;
  }
  else
  {
    //             ----------------- via encode transform
    //             (t = s) = (r = r)
    // ----- REFL  ------------------ SYMM
    // r = r       (r = r) = (t = s)
    // ---------------------------------- EQ_RESOLVE
    // t = s
    RewriteDbNodeConverter rdnc(nodeManager());
    Node eq1t = rdnc.convert(eq1);
    Assert(eq1t.getKind() == Kind::EQUAL);
    if (eq1t[0] != eq1t[1])
    {
      return false;
    }
    Node equiv = eq1.eqNode(eq1t);
    ensureProofForEncodeTransform(cdp, eq1, eq1t);
    Node equivs = eq1t.eqNode(eq1);
    cdp->addStep(equivs, ProofRule::SYMM, {equiv}, {});
    cdp->addStep(eq1t, ProofRule::REFL, {}, {eq1t[0]});
    cdp->addStep(eq1, ProofRule::EQ_RESOLVE, {eq1t, equivs}, {});
  }
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(lhs, cargs);
  Node eq2 = lhs[1].eqNode(lhs[1]);
  Node eq3 = lhs[2].eqNode(lhs[2]);
  cdp->addStep(eq2, ProofRule::REFL, {}, {lhs[1]});
  cdp->addStep(eq3, ProofRule::REFL, {}, {lhs[2]});
  Node lhsm = nm->mkNode(Kind::STRING_SUBSTR, cm, lhs[1], lhs[2]);
  Node eqLhs = lhs.eqNode(lhsm);
  cdp->addStep(eqLhs, cr, {eq1, eq2, eq3}, cargs);
  Node eqm = lhsm.eqNode(rhs);
  // Note that this is not marked simple, since it may require length
  // entailment to prove.
  // Note that there are three cases of string rewrites handled by this macro,
  // where we expect this trusted step to be filled by one of 3 RARE rewrites,
  // namely:
  // str-substr-len-include, str-substr-len-include-pre, str-substr-len-skip.
  cdp->addTrustedStep(eqm, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  Trace("brc-macro") << "- rely on rewrite " << eqm << std::endl;
  cdp->addStep(eq, ProofRule::TRANS, {eqLhs, eqm}, {});
  return true;
}


bool BasicRewriteRCons::ensureProofMacroStrEqLenUnifyPrefix(CDProof* cdp,
                                                            const Node& eq)
{
  Trace("brc-macro") << "Expand macro str eq len unify prefix " << eq
                     << std::endl;
  NodeManager* nm = nodeManager();
  theory::strings::ArithEntail ae(nm, nullptr);
  theory::strings::StringsEntail sent(nullptr, ae);

  Assert(eq[1].getKind() == Kind::AND);
  Node eq1p = eq[1];
  // get the equations equal empty
  // we group (and (= s t) (= t1 "") ... (= tn "")) to
  // (and (= s t) (and (= t1 "") ... (= tn ""))) and store in eq1p.
  std::vector<Node> empeqs;
  if (eq[1].getNumChildren() > 2)
  {
    empeqs.insert(empeqs.end(), eq[1].begin() + 1, eq[1].end());
    Node eq1g = nm->mkAnd(empeqs);
    eq1p = nm->mkNode(Kind::AND, eq[1][0], eq1g);
    Node eqg = eq1p.eqNode(eq[1]);
    cdp->addStep(eqg, ProofRule::ACI_NORM, {}, {eqg});
  }
  else
  {
    empeqs.push_back(eq[1][1]);
  }

  // prove eq[0] => eq1p in cdfwd
  CDProof cdfwd(d_env);
  Node eqsrc = eq[0];
  Node ret = sent.inferEqsFromContains(eqsrc[0], eqsrc[1]);
  Trace("brc-macro") << "[1] setup forward implication" << std::endl;
  bool eqFlipped = false;
  if (ret.isNull())
  {
    Trace("brc-macro") << "...failed " << ret << ", try flip" << std::endl;
    eqsrc = eq[0][1].eqNode(eq[0][0]);
    ret = sent.inferEqsFromContains(eqsrc[0], eqsrc[1]);
    if (ret.isNull())
    {
      Trace("brc-macro") << "... failed to replicate " << ret << std::endl;
      return false;
    }
    eqFlipped = true;
    cdfwd.addStep(eqsrc, ProofRule::SYMM, {eq[0]}, {});
  }
  Node len1 = nm->mkNode(Kind::STRING_LENGTH, eqsrc[0]);
  Node len2 = nm->mkNode(Kind::STRING_LENGTH, eqsrc[1]);
  Node leneq = proveCong(&cdfwd, len1, {eqsrc});
  Node li[2];
  std::vector<Node> eqi;
  eqi.resize(2);
  for (size_t i = 0; i < 2; i++)
  {
    Node l = i == 0 ? len1 : len2;
    TConvProofGenerator tcpg(d_env, nullptr);
    li[i] = ae.rewriteLengthIntro(l, &tcpg);
    if (li[i] != l)
    {
      Node equiv = l.eqNode(li[i]);
      std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(equiv);
      cdfwd.addProof(pfn);
      eqi[i] = pfn->getResult();
    }
  }
  Node leneqi = li[0].eqNode(li[1]);
  if (leneqi != leneq)
  {
    Node equiv = proveCong(&cdfwd, leneq, eqi);
    cdfwd.addStep(leneqi, ProofRule::EQ_RESOLVE, {leneq, equiv}, {});
  }
  Trace("brc-macro") << "...length: " << li[0] << " == " << li[1] << std::endl;
  // based on swapping above, we should have len1i >= len2i
  Node diff = nm->mkNode(Kind::SUB, li[1], li[0]);
  Node diffn = theory::arith::PolyNorm::getPolyNorm(diff);
  Trace("brc-macro") << "...norm diff " << diffn << std::endl;
  Node diffneqz = diffn.eqNode(nm->mkConstInt(Rational(0)));
  Node equiv = leneqi.eqNode(diffneqz);
  if (!ensureProofArithPolyNormRel(&cdfwd, equiv))
  {
    Trace("brc-macro") << "... failed poly norm rel" << std::endl;
    return false;
  }
  cdfwd.addStep(diffneqz, ProofRule::EQ_RESOLVE, {leneqi, equiv}, {});
  Trace("brc-macro") << "...have " << diffneqz << std::endl;

  // get the concatenation term corresponding to the components equated to empty
  std::vector<Node> concat;
  std::map<Node, Node> empMap;
  Assert(eq1p.getKind() == Kind::AND && eq1p.getNumChildren() == 2);
  for (const Node& ee : empeqs)
  {
    Assert(ee.getKind() == Kind::EQUAL && ee[0].getType().isStringLike());
    concat.push_back(ee[0]);
    empMap[ee[0]] = ee;
  }
  TypeNode stype = concat[0].getType();
  Node cc = theory::strings::utils::mkConcat(concat, stype);
  Node lcc = nm->mkNode(Kind::STRING_LENGTH, cc);
  TConvProofGenerator tcpg(d_env, nullptr);
  Node lcci = ae.rewriteLengthIntro(lcc, &tcpg);
  Trace("brc-macro") << "...normalized concat length " << lcci << std::endl;
  Node lcceq = lcc.eqNode(lcci);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(lcceq);
  cdfwd.addProof(pfn);

  // the length of the empty components should be equal to the difference
  // the length of the equality before and after removing empty components
  Node pnEq = lcci.eqNode(diffneqz[0]);
  if (!cdfwd.addStep(pnEq, ProofRule::ARITH_POLY_NORM, {}, {pnEq}))
  {
    Trace("brc-macro") << "...fail poly norm " << pnEq << std::endl;
    return false;
  }
  Node pnEq2 = lcc.eqNode(diffneqz[1]);
  cdfwd.addStep(pnEq2, ProofRule::TRANS, {lcceq, pnEq, diffneqz}, {});
  // now have proven (str.len (str.++ t1 ... tn)) = 0,
  // need t1 = "" ^ ... ^ tn = ""
  Trace("brc-macro") << "...have " << pnEq2 << std::endl;
  Node eqconv = pnEq2.eqNode(eq1p[1]);
  Trace("brc-macro") << "- subgoal " << eqconv << std::endl;
  // subgoal, which can be filled with RARE rules
  // str-len-eq-zero-concat-rec and str-len-eq-zero-base
  cdfwd.addTrustedStep(eqconv, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdfwd.addStep(eq1p[1], ProofRule::EQ_RESOLVE, {pnEq2, eqconv}, {});

  // proves (=> (and t="") (= (= (str.++ s t) r) (= s r)))
  CDProof cdmid(d_env);
  Node srcRew = eqsrc[1];
  Trace("brc-macro") << "[2] source term to rewrite " << srcRew << std::endl;
  Assert(srcRew.getKind() == Kind::STRING_CONCAT);
  std::vector<Node> eqe;
  std::map<Node, Node>::iterator it;
  for (const Node& tc : srcRew)
  {
    it = empMap.find(tc);
    if (it != empMap.end())
    {
      eqe.push_back(it->second);
    }
    else
    {
      eqe.push_back(Node::null());
    }
  }
  Node cres = proveCong(&cdmid, srcRew, eqe);
  if (cres.isNull())
  {
    Trace("brc-macro") << "...fail cong" << std::endl;
    return false;
  }
  Trace("brc-macro") << "...cong to " << cres[1] << std::endl;
  Node tgtRew = eq1p[0][eqFlipped ? 0 : 1];
  Trace("brc-macro") << "...target is " << tgtRew << std::endl;

  Node eqacin = cres[1].eqNode(tgtRew);
  if (!cdmid.addStep(eqacin, ProofRule::ACI_NORM, {}, {eqacin}))
  {
    Trace("brc-macro") << "...fail aci norm" << std::endl;
    return false;
  }
  Trace("brc-macro") << "...proved subs empty " << eqacin << std::endl;
  Node teq = srcRew.eqNode(tgtRew);
  cdmid.addStep(teq, ProofRule::TRANS, {cres, eqacin}, {});

  Node eqqeq = eq[0].eqNode(eq1p[0]);
  std::vector<Node> eqee;
  for (size_t i = 0; i < 2; i++)
  {
    Node eee = eq[0][i].eqNode(eq1p[0][i]);
    eqee.push_back(eee);
    if (eee[0] == eee[1])
    {
      Node refl = eee[0].eqNode(eee[0]);
      cdmid.addStep(refl, ProofRule::REFL, {}, {eee[0]});
    }
  }
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(eq[0], cargs);
  cdmid.addStep(eqqeq, cr, eqee, cargs);
  Node implMid = nm->mkNode(Kind::IMPLIES, eq1p[1], eqqeq);
  cdmid.addStep(implMid, ProofRule::SCOPE, {eqqeq}, empeqs);
  Trace("brc-macro") << "...intermediate result: " << implMid << std::endl;
  std::shared_ptr<ProofNode> pfmid = cdmid.getProofFor(implMid);
  Assert(implMid[1][0] == eq[0]);
  Assert(implMid[1][1] == eq1p[0]);

  // finish the forward proof
  cdfwd.addProof(pfmid);
  cdfwd.addStep(implMid[1], ProofRule::MODUS_PONENS, {eq1p[1], implMid}, {});
  cdfwd.addStep(eq1p[0], ProofRule::EQ_RESOLVE, {eq[0], implMid[1]}, {});
  cdfwd.addStep(eq1p, ProofRule::AND_INTRO, {eq1p[0], eq1p[1]}, {});
  Node impl = nm->mkNode(Kind::IMPLIES, eq[0], eq1p);
  cdfwd.addStep(impl, ProofRule::SCOPE, {eq1p}, {eq[0]});
  cdp->addProof(cdfwd.getProofFor(impl));

  // reverse proof is easy
  CDProof cdrev(d_env);
  cdrev.addProof(pfmid);
  cdrev.addStep(implMid[1], ProofRule::MODUS_PONENS, {eq1p[1], implMid}, {});
  Node equivs = implMid[1][1].eqNode(implMid[1][0]);
  cdrev.addStep(equivs, ProofRule::SYMM, {implMid[1]}, {});
  cdrev.addStep(
      implMid[1][0], ProofRule::EQ_RESOLVE, {implMid[1][1], equivs}, {});
  Node implrev = nm->mkNode(Kind::IMPLIES, eq1p, eq[0]);
  cdrev.addStep(implrev, ProofRule::SCOPE, {eq[0]}, {eq1p[0], eq1p[1]});
  cdp->addProof(cdrev.getProofFor(implrev));

  // dual implication
  Node eqfinal = proveDualImplication(cdp, impl, implrev);

  // if we grouped the empty equations, we close with a transitive step
  // which we added via ACI_NORM above
  if (eq1p != eq[1])
  {
    cdp->addStep(eq, ProofRule::TRANS, {eqfinal, eq1p.eqNode(eq[1])}, {});
  }

  return true;
}

bool BasicRewriteRCons::ensureProofMacroStrEqLenUnify(CDProof* cdp,
                                                      const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand macro str eq len unify for " << eq << std::endl;
  Assert(eq[1].getKind() == Kind::AND && eq[1].getNumChildren() == 2);
  // This proves e.g. (= (= (str.++ x y) (str.++ z w)) (and (= x z) (= y w))).
  // We prove this in two phases
  Node falsen = nodeManager()->mkConst(false);
  std::vector<Node> elhs;
  std::vector<Node> erhs;
  std::vector<Node> cpremises(eq[1].begin(), eq[1].end());
  for (const Node& eq1e : cpremises)
  {
    Assert(eq1e.getKind() == Kind::EQUAL && eq1e[0].getType().isStringLike());
    elhs.push_back(eq1e[0]);
    erhs.push_back(eq1e[1]);
  }
  // the proper grouped equality
  CDProof cdfwd(d_env);
  Node clhs = nm->mkNode(Kind::STRING_CONCAT, elhs);
  Node crhs = nm->mkNode(Kind::STRING_CONCAT, erhs);
  Node ceq = clhs.eqNode(crhs);
  // NOTE: ceq could be proven equivalent to eq[0]

  Node llhs0 = nm->mkNode(Kind::STRING_LENGTH, elhs[0]);
  Node lrhs0 = nm->mkNode(Kind::STRING_LENGTH, erhs[0]);
  Node leq = llhs0.eqNode(lrhs0);
  // should be provable as a subgoal
  Trace("brc-macro") << "- subgoal " << leq << std::endl;
  cdfwd.addTrustedStep(leq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  // prove first component by CONCAT_UNIFY
  cdfwd.addStep(cpremises[0], ProofRule::CONCAT_UNIFY, {ceq, leq}, {falsen});

  elhs[0] = erhs[0];
  Node clhs2 = nm->mkNode(Kind::STRING_CONCAT, elhs);
  std::vector<Node> cargs;
  ProofRule ccr = expr::getCongRule(clhs2, cargs);
  Node equiv = clhs2.eqNode(clhs);
  Node cp0s = cpremises[0][1].eqNode(cpremises[0][0]);
  Node reflEq = elhs[1].eqNode(elhs[1]);
  cdfwd.addStep(cp0s, ProofRule::SYMM, {cpremises[0]}, {});
  cdfwd.addStep(reflEq, ProofRule::REFL, {}, {elhs[1]});
  cdfwd.addStep(equiv, ccr, {cp0s, reflEq}, cargs);
  Node equiv2 = clhs2.eqNode(crhs);
  cdfwd.addStep(equiv2, ProofRule::TRANS, {equiv, ceq}, {});
  // prove second component by CONCAT_EQ after congruence above
  cdfwd.addStep(cpremises[1], ProofRule::CONCAT_EQ, {equiv2}, {falsen});
  // combine two equalities
  cdfwd.addStep(eq[1], ProofRule::AND_INTRO, cpremises, {});
  // prove the implication and add to main proof
  Node impl = nm->mkNode(Kind::IMPLIES, ceq, eq[1]);
  cdfwd.addStep(impl, ProofRule::SCOPE, {eq[1]}, {ceq});
  cdp->addProof(cdfwd.getProofFor(impl));

  // reverse proof is easy
  CDProof cdrev(d_env);
  cdrev.addStep(
      cpremises[0], ProofRule::AND_ELIM, {eq[1]}, {nm->mkConstInt(0)});
  cdrev.addStep(
      cpremises[1], ProofRule::AND_ELIM, {eq[1]}, {nm->mkConstInt(1)});
  cargs.clear();
  ccr = expr::getCongRule(ceq[0], cargs);
  cdrev.addStep(ceq, ccr, cpremises, cargs);
  // prove the implication and add to main proof
  Node implrev = nm->mkNode(Kind::IMPLIES, eq[1], ceq);
  cdrev.addStep(implrev, ProofRule::SCOPE, {ceq}, {eq[1]});
  cdp->addProof(cdrev.getProofFor(implrev));

  // now prove dual implication is the same as equality
  Node eqfinal = proveDualImplication(cdp, impl, implrev);

  // prove eq[0] is equal to the grouped concatenation terms, if necessary
  if (eq[0] != ceq)
  {
    Node eqs1 = eq[0][0].eqNode(clhs);
    Trace("brc-macro") << "- subgoal " << eqs1 << std::endl;
    cdp->addTrustedStep(eqs1, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    Node eqs2 = eq[0][1].eqNode(crhs);
    Trace("brc-macro") << "- subgoal " << eqs2 << std::endl;
    cdp->addTrustedStep(eqs2, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    Node equivSetup = eq[0].eqNode(ceq);
    cargs.clear();
    ccr = expr::getCongRule(eq[0], cargs);
    cdp->addStep(equivSetup, ccr, {eqs1, eqs2}, cargs);
    cdp->addStep(eq, ProofRule::TRANS, {equivSetup, eqfinal}, {});
  }
  else
  {
    Assert(eqfinal == eq);
  }
  return true;
}

bool BasicRewriteRCons::ensureProofMacroOverlap(ProofRewriteRule id,
                                                CDProof* cdp,
                                                const Node& eq)
{
  Trace("brc-macro") << "Expand macro overlap (" << id << ") for " << eq
                     << std::endl;
  NodeManager* nm = nodeManager();
  Assert(eq[0].getNumChildren() >= 2);
  Node concat = eq[0][0];
  TypeNode stype = concat.getType();
  Node emp = theory::strings::Word::mkEmptyWord(stype);
  size_t nchildpre = 0;
  ProofRewriteRule rule;
  std::vector<Node> premises;
  if (id == ProofRewriteRule::MACRO_STR_SPLIT_CTN)
  {
    Assert(concat.getKind() == Kind::STRING_CONCAT);
    rule = ProofRewriteRule::STR_OVERLAP_SPLIT_CTN;
    Assert(eq[1].getKind() == Kind::OR
           && eq[1][0].getKind() == Kind::STRING_CONTAINS);
    if (eq[1][0][0].getKind() == Kind::STRING_CONCAT)
    {
      nchildpre = eq[1][0][0].getNumChildren();
    }
    else if (eq[1][0][0] != emp)
    {
      nchildpre = 1;
    }
    // partition into three children
    std::vector<Node> childpre(concat.begin(), concat.begin() + nchildpre);
    Node cpre = theory::strings::utils::mkConcat(childpre, stype);
    Node cmid = concat[nchildpre];
    std::vector<Node> childpost(concat.begin() + nchildpre + 1, concat.end());
    Node cpost = theory::strings::utils::mkConcat(childpost, stype);
    Node cgroup = nm->mkNode(Kind::STRING_CONCAT, cpre, cmid, cpost);
    if (concat != cgroup)
    {
      Node eqc = concat.eqNode(cgroup);
      if (!cdp->addStep(eqc, ProofRule::ACI_NORM, {}, {eqc}))
      {
        Assert(false);
        return false;
      }
      premises.push_back(eqc);
    }
  }
  else
  {
    Assert(id == ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS);
    theory::strings::ArithEntail ae(nm, nullptr);
    theory::strings::StringsEntail se(nullptr, ae);
    theory::strings::SequencesRewriter srew(nm, ae, se, nullptr);
    std::vector<Node> nb, nc1, ne;
    // replay the strip endpoint operation
    Kind k = eq[0].getKind();
    Node res = srew.rewriteViaMacroStrStripEndpoints(eq[0], nb, nc1, ne);
    if (res != eq[1])
    {
      Assert(false);
      return false;
    }
    std::vector<Node> nc2;
    theory::strings::utils::getConcat(eq[0][1], nc2);
    std::vector<Node> newChildren[2];
    for (size_t i = 0; i < 2; i++)
    {
      std::vector<Node>& vec = i == 0 ? nb : ne;
      if (i == 0 && k == Kind::STRING_INDEXOF)
      {
        Assert(vec.empty());
        continue;
      }
      else if (i == 1)
      {
        // placeholder for the middle term
        newChildren[0].push_back(emp);
        newChildren[1].push_back(emp);
      }
      if (vec.empty())
      {
        newChildren[0].push_back(emp);
        newChildren[1].push_back(emp);
        continue;
      }
      if (vec.size() != 1)
      {
        Trace("brc-macro") << "...fail due to multiple stripped components"
                           << std::endl;
        Assert(false);
        return false;
      }
      newChildren[0].push_back(vec[0]);
      // should be the case since we don't rewrite from both sides if
      // the second term is a constant.
      Assert(!nc2.empty());
      size_t index2 = (i == 0 ? 0 : nc2.size() - 1);
      if (i == 0)
      {
        newChildren[1].push_back(nc2[index2]);
        nc2.erase(nc2.begin(), nc2.begin() + 1);
      }
      else
      {
        newChildren[1].push_back(nc2[index2]);
        nc2.pop_back();
      }
    }
    size_t remIndex = k == Kind::STRING_INDEXOF ? 0 : 1;
    newChildren[0][remIndex] = theory::strings::utils::mkConcat(nc1, stype);
    newChildren[1][remIndex] = theory::strings::utils::mkConcat(nc2, stype);
    Trace("brc-macro") << "First child processed to : " << eq[0][0]
                       << " == " << newChildren[0] << std::endl;
    Trace("brc-macro") << "Second child processed to : " << eq[0][1]
                       << " == " << newChildren[1] << std::endl;
    // now, check if the children changed, if so add to premises
    Node g1 = theory::strings::utils::mkConcat(newChildren[0], stype);
    Node g2 = theory::strings::utils::mkConcat(newChildren[1], stype);
    // the first may involve more than ACI_NORM, we use a subgoal
    if (g1 != eq[0][0])
    {
      Node eqc = eq[0][0].eqNode(g1);
      cdp->addTrustedStep(
          eqc, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      premises.push_back(eqc);
    }
    // the second should just be ACI_NORM
    if (g2 != eq[0][1])
    {
      // add the REFL step if we didnt change above
      if (g1 == eq[0][0])
      {
        Node refl = eq[0][0].eqNode(eq[0][0]);
        cdp->addStep(refl, ProofRule::REFL, {}, {eq[0][0]});
        premises.push_back(refl);
      }
      Node eqc = eq[0][1].eqNode(g2);
      if (!cdp->addStep(eqc, ProofRule::ACI_NORM, {}, {eqc}))
      {
        Assert(false);
        Trace("brc-macro") << "...failed ACI_NORM" << std::endl;
        return false;
      }
      premises.push_back(eqc);
    }
    switch (k)
    {
      case Kind::STRING_CONTAINS:
        rule = ProofRewriteRule::STR_OVERLAP_ENDPOINTS_CTN;
        break;
      case Kind::STRING_INDEXOF:
        rule = ProofRewriteRule::STR_OVERLAP_ENDPOINTS_INDEXOF;
        break;
      case Kind::STRING_REPLACE:
        rule = ProofRewriteRule::STR_OVERLAP_ENDPOINTS_REPLACE;
        break;
      default: return false;
    }
  }
  // cgroup is now the proper version of concat and we have proved (if
  // necessary) that concat = cgroup.
  Node input = eq[0];
  // if we rewrote children above
  std::vector<Node> transEq;
  if (!premises.empty())
  {
    // prove input = inputRew by congruence given the premises
    Node ceq = proveCong(cdp, input, premises);
    transEq.push_back(ceq);
    input = ceq[1];
  }
  Trace("brc-macro") << "Run " << rule << " on " << input << std::endl;
  theory::Rewriter* rr = d_env.getRewriter();
  Node ret = rr->rewriteViaRule(rule, input);
  if (ret.isNull())
  {
    Trace("brc-macro") << "...failed rewrite" << std::endl;
    return false;
  }
  // add the rewrite
  Node equiv = input.eqNode(ret);
  cdp->addTheoryRewriteStep(equiv, rule);
  transEq.push_back(equiv);
  if (ret != eq[1])
  {
    // should rewrite e.g. via ACI_NORM
    Node eqpost = ret.eqNode(eq[1]);
    Trace("brc-macro") << "- post-process subgoal " << eqpost << std::endl;
    cdp->addTrustedStep(
        eqpost, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(eqpost);
  }
  // apply transitivity if necessary
  if (transEq.size() > 1)
  {
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  }
  return true;
}

bool BasicRewriteRCons::ensureProofMacroStrComponentCtn(CDProof* cdp,
                                                        const Node& eq)
{
  Trace("brc-macro") << "Expand macro str component ctn " << eq << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_CONTAINS);
  theory::strings::ArithEntail ae(nodeManager(), nullptr);
  theory::strings::StringsEntail se(nullptr, ae);
  std::vector<Node> nc1, nc2;
  theory::strings::utils::getConcat(eq[0][0], nc1);
  theory::strings::utils::getConcat(eq[0][1], nc2);
  std::vector<Node> nc1rb, nc1re;
  if (se.componentContains(nc1, nc2, nc1rb, nc1re, true) == -1)
  {
    return false;
  }
  Trace("brc-macro") << "...paritioned to " << nc1rb << " " << nc1 << " "
                     << nc1re << std::endl;
  // group the LHS so that it contains the RHS verbatim as the middle child
  // for example (str.contains (str.++ x y z w) (str.++ y z)) --->
  // (str.contains (str.++ x (str.++ y z) w) (str.++ y z))
  TypeNode stype = eq[0][0].getType();
  NodeManager* nm = nodeManager();
  std::vector<Node> cc;
  if (!nc1rb.empty())
  {
    cc.push_back(theory::strings::utils::mkConcat(nc1rb, stype));
  }
  if (!nc1.empty())
  {
    cc.push_back(theory::strings::utils::mkConcat(nc1, stype));
  }
  if (!nc1re.empty())
  {
    cc.push_back(theory::strings::utils::mkConcat(nc1re, stype));
  }
  Node cg = theory::strings::utils::mkConcat(cc, stype);
  Node equiv = eq[0][0].eqNode(cg);
  cdp->addTrustedStep(
      equiv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  std::vector<Node> cargs;
  ProofRule cr = expr::getCongRule(eq[0], cargs);
  Node refl = eq[0][1].eqNode(eq[0][1]);
  Node ctng = nm->mkNode(Kind::STRING_CONTAINS, cg, eq[0][1]);
  Node eq1 = eq[0].eqNode(ctng);
  cdp->addStep(refl, ProofRule::REFL, {}, {eq[0][1]});
  cdp->addStep(eq1, cr, {equiv, refl}, cargs);
  Node eq2 = ctng.eqNode(eq[1]);
  cdp->addTrustedStep(eq2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(eq, ProofRule::TRANS, {eq1, eq2}, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroStrConstNCtnConcat(CDProof* cdp,
                                                           const Node& eq)
{
  Trace("brc-macro") << "Expand macro str const nctn concat " << eq
                     << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_CONTAINS);
  NodeManager* nm = nodeManager();
  // We assume eq[0] is true and derive a contradiction. This is based
  // on (str.contains s t) => (= s (str.++ k1 t k2)) by string eager reduction,
  // (str.++ k1 t k2) in (re.++ Sigma* (str.to_re t) Sigma*) and
  // ~ s in (re.++ Sigma* (str.to_re t) Sigma*).
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node er = pc->checkDebug(ProofRule::STRING_EAGER_REDUCTION, {}, {eq[0]});
  Assert(!er.isNull());
  cdp->addStep(er, ProofRule::STRING_EAGER_REDUCTION, {}, {eq[0]});
  Trace("brc-macro") << "...eager reduce: " << er << std::endl;
  Node truen = nm->mkConst(true);
  Node eqt = eq[0].eqNode(truen);
  cdp->addStep(eqt, ProofRule::TRUE_INTRO, {eq[0]}, {});
  Node eqi = proveCong(cdp, er, {eqt});
  if (eqi.isNull())
  {
    Trace("brc-macro") << "...failed cong" << std::endl;
    Assert(false);
    return false;
  }
  Trace("brc-macro") << "...cong " << eqi << std::endl;
  AlwaysAssert(eqi[1].getKind() == Kind::ITE);
  Node eqi2 = eqi[1].eqNode(eqi[1][1]);
  cdp->addTrustedStep(eqi2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});

  Node ere = er.eqNode(eqi[1][1]);
  cdp->addStep(ere, ProofRule::TRANS, {eqi, eqi2}, {});
  cdp->addStep(eqi[1][1], ProofRule::EQ_RESOLVE, {er, ere}, {});

  // flatten
  Node concat = eqi[1][1][1];
  AlwaysAssert(concat.getKind() == Kind::STRING_CONCAT
               && concat.getNumChildren() == 3);
  std::vector<Node> cc;
  cc.push_back(concat[0]);
  cc.insert(cc.end(), concat[1].begin(), concat[1].end());
  cc.push_back(concat[2]);
  Node cf = nm->mkNode(Kind::STRING_CONCAT, cc);
  Node eqa = concat.eqNode(cf);
  if (!cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa}))
  {
    Trace("brc-macro") << "...failed ACI" << std::endl;
    Assert(false);
    return false;
  }
  Node eqsf = eqi[1][1][0].eqNode(cf);
  cdp->addStep(eqsf, ProofRule::TRANS, {eqi[1][1], eqa}, {});
  Node eqsfs = proveSymm(cdp, eqsf);
  Trace("brc-macro") << "Have : " << eqsfs << std::endl;

  Node mem = proveGeneralReMembership(cdp, cf);
  Trace("brc-macro") << "Membership : " << mem << std::endl;

  Node memc = proveCong(cdp, mem, {eqsfs});
  Trace("brc-macro") << "Cong membership : " << memc << std::endl;

  theory::Rewriter* rr = d_env.getRewriter();
  Node res = rr->rewriteViaRule(ProofRewriteRule::STR_IN_RE_EVAL, memc[1]);
  if (res.isNull() || res != eq[1])
  {
    Trace("brc-macro") << "...failed str in eval" << std::endl;
    Assert(false);
    return false;
  }
  Node eqf = memc[1].eqNode(res);
  cdp->addTheoryRewriteStep(eqf, ProofRewriteRule::STR_IN_RE_EVAL);

  Node meqf = mem.eqNode(eq[1]);
  cdp->addStep(meqf, ProofRule::TRANS, {memc, eqf}, {});

  cdp->addStep(eq[1], ProofRule::EQ_RESOLVE, {mem, meqf}, {});

  Node nctn = eq[0].notNode();
  cdp->addStep(nctn, ProofRule::SCOPE, {eq[1]}, {eq[0]});
  cdp->addStep(eq, ProofRule::FALSE_INTRO, {nctn}, {});

  return true;
}

bool BasicRewriteRCons::ensureProofMacroStrInReInclusion(CDProof* cdp,
                                                         const Node& eq)
{
  Trace("brc-macro") << "Expand macro str in re inclusion for " << eq
                     << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_IN_REGEXP);
  NodeManager* nm = nodeManager();
  Node truen = eq[1];
  Assert(truen.isConst() && truen.getConst<bool>());
  // proof by contradiction

  // start by proving e.g.
  // (str.in_re (str.++ x "A" y) (re.++ Sigma* (str.to_re "A") Sigma*))
  Node trivMemc = proveGeneralReMembership(cdp, eq[0][0]);
  Trace("brc-macro") << "Trivial membership: " << trivMemc << std::endl;

  // then take intersection with the complement of the RE given in the LHS
  Node comp = nm->mkNode(Kind::REGEXP_COMPLEMENT, eq[0][1]);
  Node inter = nm->mkNode(Kind::REGEXP_INTER, trivMemc[1], comp);
  Trace("brc-macro") << "Rewrite inclusion: " << inter << std::endl;
  theory::Rewriter* rr = d_env.getRewriter();
  Node res = rr->rewriteViaRule(ProofRewriteRule::RE_INTER_INCLUSION, inter);
  Trace("brc-macro") << "...returned " << res << std::endl;
  if (res.isNull())
  {
    Assert(false);
    return false;
  }
  // should have an RE inclusion
  Node inclusionEq = inter.eqNode(res);
  cdp->addTheoryRewriteStep(inclusionEq, ProofRewriteRule::RE_INTER_INCLUSION);

  Node memNeg = eq[0].notNode();
  Node memComp = nm->mkNode(Kind::STRING_IN_REGEXP, eq[0][0], comp);
  Node compEq = memNeg.eqNode(memComp);
  cdp->addTrustedStep(compEq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdp->addStep(memComp, ProofRule::EQ_RESOLVE, {memNeg, compEq}, {});

  Node imem = nm->mkNode(Kind::STRING_IN_REGEXP, eq[0][0], inter);
  cdp->addStep(imem, ProofRule::RE_INTER, {trivMemc, memComp}, {});

  Node meq = proveCong(cdp, imem, {Node::null(), inclusionEq});
  Assert(!meq.isNull());
  Node noneMem = meq[1];

  Node falsen = nm->mkConst(false);
  Node noneFalseEq = noneMem.eqNode(falsen);
  cdp->addTrustedStep(noneFalseEq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});

  Node imemFalse = imem.eqNode(falsen);
  cdp->addStep(imemFalse, ProofRule::TRANS, {meq, noneFalseEq}, {});
  cdp->addStep(falsen, ProofRule::EQ_RESOLVE, {imem, imemFalse}, {});

  Node memDoubleNeg = memNeg.notNode();
  cdp->addStep(memDoubleNeg, ProofRule::SCOPE, {falsen}, {memNeg});

  Node deq = memDoubleNeg.eqNode(eq[0]);
  cdp->addTrustedStep(deq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdp->addStep(eq[0], ProofRule::EQ_RESOLVE, {memDoubleNeg, deq}, {});
  cdp->addStep(eq, ProofRule::TRUE_INTRO, {eq[0]}, {});
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
    Assert(false);
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
      Assert(false);
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
          cdp->addTrustedStep(
              eqc, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
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
            Assert(false);
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
      Assert(false);
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
      Assert(false);
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
    Assert(false);
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
    Assert(false);
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
    Assert(false);
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
  cdp->addTheoryRewriteStep(eqq, ProofRewriteRule::QUANT_VAR_ELIM_EQ);
  finalTransEq.push_back(eqq);
  Node beq = body1.eqNode(body2);
  cdp->addStep(beq, ProofRule::TRANS, finalTransEq, {});
  return true;
}

bool BasicRewriteRCons::ensureProofMacroQuantVarElimIneq(CDProof* cdp,
                                                         const Node& eq)
{
  Trace("brc-macro") << "Expand macro quant var elim ineq " << eq << std::endl;
  // get info on the right hand side
  std::unordered_set<Node> varsRhs;
  std::vector<Node> litsRhs;
  Node body = eq[1];
  if (eq[1].getKind() == Kind::FORALL)
  {
    varsRhs.insert(eq[1][0].begin(), eq[1][0].end());
    body = eq[1][1];
  }
  if (body.getKind() == Kind::OR)
  {
    litsRhs.insert(litsRhs.end(), body.begin(), body.end());
  }
  else if (!body.isConst())
  {
    litsRhs.push_back(body);
  }
  // determine the variable that was eliminated
  Assert(eq[0].getKind() == Kind::FORALL);
  Node elimVar;
  for (const Node& v : eq[0][0])
  {
    if (varsRhs.find(v) == varsRhs.end())
    {
      elimVar = v;
      break;
    }
  }
  if (elimVar.isNull())
  {
    return false;
  }
  std::vector<Node> elimLits;
  std::vector<Node> keepLits;
  if (eq[0][1].getKind() == Kind::OR)
  {
    for (const Node& lit : eq[0][1])
    {
      if (std::find(litsRhs.begin(), litsRhs.end(), lit) == litsRhs.end())
      {
        elimLits.push_back(lit);
      }
      else
      {
        keepLits.push_back(lit);
      }
    }
  }
  else
  {
    Assert(litsRhs.empty());
    elimLits.push_back(eq[0][1]);
  }
  Assert(!elimLits.empty());
  Trace("brc-macro") << "Eliminated variable: " << elimVar << std::endl;
  Trace("brc-macro") << "Eliminated lits: " << elimLits << std::endl;
  Trace("brc-macro") << "Keep lits: " << keepLits << std::endl;
  NodeManager* nm = nodeManager();
  if (eq[0][0].getNumChildren() > 1)
  {
    // note that keepLits may be empty, e.g. for
    // forall xy. x > y ---> forall y. false
    Node bvle = nm->mkNode(Kind::BOUND_VAR_LIST, elimVar);
    Node kdisj = nm->mkOr(keepLits);
    Node edisj = nm->mkOr(elimLits);
    Node lhsq = nm->mkNode(Kind::FORALL, bvle, eq[0][1]);
    Trace("brc-macro") << "...Start with " << lhsq << std::endl;
    Node por = nm->mkNode(Kind::OR, edisj, kdisj);
    std::vector<Node> transEq;
    Node lhsqg = lhsq;
    if (eq[0][1] != por)
    {
      Node equiv = eq[0][1].eqNode(por);
      if (!expr::isACINorm(eq[0][1], por))
      {
        return false;
      }
      cdp->addStep(equiv, ProofRule::ACI_NORM, {}, {equiv});
      Node rhsq = nm->mkNode(Kind::FORALL, bvle, por);
      Node equivc = lhsq.eqNode(rhsq);
      std::vector<Node> cargs;
      ProofRule cr = expr::getCongRule(lhsq, cargs);
      cdp->addStep(equivc, cr, {equiv}, cargs);
      transEq.push_back(equivc);
      lhsqg = rhsq;
      Trace("brc-macro") << "...ACI_NORM to " << lhsq << std::endl;
    }
    theory::Rewriter* rr = d_env.getRewriter();
    Node mq = rr->rewriteViaRule(ProofRewriteRule::QUANT_MINISCOPE_OR, lhsqg);
    if (mq.isNull())
    {
      return false;
    }
    Assert(mq != lhsqg);
    Node equiv = lhsqg.eqNode(mq);
    cdp->addTheoryRewriteStep(equiv, ProofRewriteRule::QUANT_MINISCOPE_OR);
    transEq.push_back(equiv);
    Trace("brc-macro") << "...miniscope to " << mq << std::endl;
    if (mq.getKind() != Kind::OR || mq.getNumChildren() != 2)
    {
      return false;
    }
    Node qvi =
        rr->rewriteViaRule(ProofRewriteRule::MACRO_QUANT_VAR_ELIM_INEQ, mq[0]);
    if (qvi.isNull() || !qvi.isConst())
    {
      return false;
    }
    Assert(!qvi.getConst<bool>());
    std::vector<Node> cpremises;
    cpremises.push_back(mq[0].eqNode(qvi));
    cpremises.push_back(mq[1].eqNode(mq[1]));
    // immediately call this method again, which should not make any further
    // recursive call.
    if (!ensureProofMacroQuantVarElimIneq(cdp, cpremises[0]))
    {
      return false;
    }
    cdp->addStep(cpremises[1], ProofRule::REFL, {}, {mq[1]});
    Node mqf = nm->mkNode(Kind::OR, qvi, mq[1]);
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(mq, cargs);
    equiv = mq.eqNode(mqf);
    cdp->addStep(equiv, cr, cpremises, cargs);
    transEq.push_back(equiv);
    Trace("brc-macro") << "...rewrite ineq (again) to " << mqf << std::endl;
    equiv = mqf.eqNode(mq[1]);
    cdp->addTrustedStep(
        equiv, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(equiv);
    Trace("brc-macro") << "...rewrite (simple) to " << mq[1] << std::endl;
    Node eqBody = lhsq.eqNode(mq[1]);
    cdp->addStep(eqBody, ProofRule::TRANS, transEq, {});
    transEq.clear();
    Assert(eq[1].getKind() == Kind::FORALL);

    // now add back outermost variables
    Node bcLhs = nm->mkNode(Kind::FORALL, eq[1][0], eqBody[0]);
    Node bcLhsm =
        rr->rewriteViaRule(ProofRewriteRule::QUANT_MERGE_PRENEX, bcLhs);
    if (bcLhsm != eq[0])
    {
      // likely reorder?
      equiv = eq[0].eqNode(bcLhsm);
      if (!cdp->addStep(equiv, ProofRule::QUANT_VAR_REORDERING, {}, {equiv}))
      {
        Trace("brc-macro") << "...failed eq lhs" << std::endl;
        return false;
      }
      transEq.push_back(equiv);
    }
    equiv = bcLhs.eqNode(bcLhsm);
    cdp->addTheoryRewriteStep(equiv, ProofRewriteRule::QUANT_MERGE_PRENEX);
    equiv = bcLhsm.eqNode(bcLhs);
    cdp->addStep(equiv, ProofRule::SYMM, {equiv}, {});
    transEq.push_back(equiv);
    Node bcRhs = nm->mkNode(Kind::FORALL, eq[1][0], eqBody[1]);
    if (bcRhs != eq[1])
    {
      Trace("brc-macro") << "...failed eq rhs" << std::endl;
      return false;
    }
    cargs.clear();
    cr = expr::getCongRule(bcLhs, cargs);
    equiv = bcLhs.eqNode(bcRhs);
    cdp->addStep(equiv, cr, {eqBody}, cargs);
    transEq.push_back(equiv);
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
    return true;
  }

  // find the instantiation term
  std::vector<Node> normLits;
  bool isUpper = true;
  bool isUpperSet = false;
  TConvProofGenerator tcpg(d_env);
  std::vector<Node> negLits;
  for (const Node& lit : elimLits)
  {
    Trace("brc-macro") << "process elim lit: " << lit << std::endl;
    Node negLit = lit.negate();
    negLits.push_back(negLit);
    bool pol = lit.getKind() != Kind::NOT;
    Node atom = pol ? lit : lit[0];
    // isolate
    std::map<Node, Node> msum;
    if (!theory::ArithMSum::getMonomialSumLit(atom, msum))
    {
      return false;
    }
    // store that this literal is upper/lower bound for itm->first
    Kind k = atom.getKind();
    Node veq_c;
    Node val;
    int ires = theory::ArithMSum::isolate(elimVar, msum, veq_c, val, k);
    if (ires == 0 || !veq_c.isNull())
    {
      Trace("brc-macro") << "...failed isolate" << std::endl;
      return false;
    }
    Trace("brc-macro") << "... processes to " << elimVar << " <> " << val
                       << std::endl;
    // rewrite it, should be provable with ARITH_POLY_NORM since monomials
    // should be already rewritten.
    val = rewrite(val);
    Node nlit;
    if (k == Kind::GEQ)
    {
      bool isUpperCurr = pol == (ires == 1);
      if (isUpperSet && isUpper != isUpperCurr)
      {
        return false;
      }
      isUpper = isUpperCurr;
      isUpperSet = true;
      Trace("brc-macro") << "...is_upper = " << isUpperCurr << std::endl;
      if (ires < 0)
      {
        k = Kind::LEQ;
      }
      if (pol)
      {
        k = theory::arith::negateKind(k);
      }
      nlit = nm->mkNode(k, elimVar, val);
    }
    else
    {
      Assert(k == Kind::EQUAL && pol);
      nlit = nm->mkNode(Kind::EQUAL, elimVar, val).notNode();
    }
    Trace("brc-macro") << "...nlit is " << nlit << std::endl;
    Trace("brc-macro") << "......from " << negLit << std::endl;
    normLits.push_back(nlit);
    if (negLit != nlit)
    {
      Trace("brc-macro") << "- rewrite " << negLit << " -> " << nlit
                         << std::endl;
      // should be provable by REFL or ARITH_POLY_NORM_REL
      tcpg.addRewriteStep(negLit,
                          nlit,
                          nullptr,
                          false,
                          TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
    }
  }
  Node eqnorm;
  Node qnorm;
  // In the following, we update (or ~L1 ... ~Ln) to (=> (and L1 ... Ln) false)
  // and then prove (and L1 ... Ln). This makes it easier to match to existing
  // rules.
  // not necessary if single literal
  if (normLits.size() > 1)
  {
    Node negBody = eq[0][1].negate();
    Node negPremise = nm->mkAnd(negLits);
    if (negBody != negPremise)
    {
      Trace("brc-macro") << "- rewrite de-morgan " << negBody << " -> "
                         << negPremise << std::endl;
      // by de-morgan
      tcpg.addRewriteStep(negBody,
                          negPremise,
                          nullptr,
                          true,
                          TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
    }
    Node negRew = nm->mkNode(Kind::IMPLIES, negBody, nm->mkConst(false));
    // F = (=> (not F) false)
    Trace("brc-macro") << "- rewrite impl intro " << eq[0][1] << " -> "
                       << negRew << std::endl;
    tcpg.addRewriteStep(eq[0][1],
                        negRew,
                        nullptr,
                        true,
                        TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE);
    Trace("brc-macro") << "...from " << eq[0] << std::endl;
    std::shared_ptr<ProofNode> pfn = tcpg.getProofForRewriting(eq[0]);
    eqnorm = pfn->getResult();
    qnorm = eqnorm[1];
    cdp->addProof(pfn);
    Trace("brc-macro") << "...normalized to " << qnorm << std::endl;
  }
  else
  {
    qnorm = eq[0];
  }
  // Now have upper set. note if all disequalities we don't care about the
  // value of isUpper
  std::reverse(normLits.begin(), normLits.end());
  // make the max or min of all terms based on isUpper
  Node iterm;
  for (const Node& nl : normLits)
  {
    Node atom = nl.getKind() == Kind::NOT ? nl[0] : nl;
    Trace("brc-macro") << "...process normalized atom " << atom << std::endl;
    Kind k = atom.getKind();
    Node itc = atom[1];
    if (k != Kind::GEQ && k != Kind::LEQ)
    {
      itc = rewrite(nm->mkNode(
          Kind::ADD,
          itc,
          nm->mkConstRealOrInt(itc.getType(), Rational(isUpper ? -1 : 1))));
    }
    if (iterm.isNull())
    {
      iterm = itc;
    }
    else
    {
      iterm = nm->mkNode(Kind::ITE,
                         nm->mkNode(isUpper ? Kind::LT : Kind::GEQ, itc, iterm),
                         itc,
                         iterm);
    }
  }
  Trace("brc-macro") << "Instantiation term is: " << iterm << std::endl;
  // instantiate
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node iarg = nm->mkNode(Kind::SEXPR, iterm);
  Assert(qnorm[0].getNumChildren() == 1);
  Trace("brc-macro") << "Instantiate: " << qnorm << " / " << iarg << std::endl;
  Node inst = pc->checkDebug(ProofRule::INSTANTIATE, {qnorm}, {iarg});
  cdp->addStep(inst, ProofRule::INSTANTIATE, {qnorm}, {iarg});
  Trace("brc-macro") << "Have instantiation: " << inst << std::endl;
  Node falsen = nm->mkConst(false);
  if (normLits.size() > 1)
  {
    Assert(inst.getKind() == Kind::IMPLIES && inst[1] == falsen);
    Assert(inst[0].getKind() == Kind::AND);
    std::vector<Node> ipremises(inst[0].begin(), inst[0].end());
    Node currTerm = iterm;
    // always have proven iterm >= currTerm
    Node src;
    size_t index = 0;
    do
    {
      Node next;
      if (index + 1 < ipremises.size())
      {
        Assert(currTerm.getKind() == Kind::ITE);
        Node p1 =
            nm->mkNode(isUpper ? Kind::LEQ : Kind::GEQ, currTerm, currTerm[1]);
        Trace("brc-macro") << "...have " << p1 << std::endl;
        Node p2 =
            nm->mkNode(isUpper ? Kind::LEQ : Kind::GEQ, currTerm, currTerm[2]);
        cdp->addTrustedStep(
            p1, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
        Trace("brc-macro") << "...have " << p2 << std::endl;
        cdp->addTrustedStep(
            p2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
        if (currTerm != iterm)
        {
          Assert(!src.isNull());
          // must prove iterm <= currTerm[2], for proving transitivity to the
          // next literals
          next = proveTransIneq(cdp, src, p2);
          // must prove iterm <= currTerm[1], for proving the current literal
          // below
          src = proveTransIneq(cdp, src, p1);
        }
        else
        {
          src = p1;
          next = p2;
        }
        currTerm = currTerm[2];
      }
      else
      {
        Trace("brc-macro") << "...base term " << currTerm << std::endl;
        // src should already be set and entail the target below
      }
      // prove
      Node tgt = ipremises[index];
      index++;
      Assert(!src.isNull());
      if (src != tgt)
      {
        proveIneqWeaken(cdp, src, tgt);
      }
      src = next;
    } while (!src.isNull());
    cdp->addStep(inst[0], ProofRule::AND_INTRO, ipremises, {});
    cdp->addStep(falsen, ProofRule::MODUS_PONENS, {inst[0], inst}, {});
  }
  else
  {
    Node ief = inst.eqNode(falsen);
    Trace("brc-macro") << "Prove (base): " << ief << std::endl;
    cdp->addTrustedStep(
        ief, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    cdp->addStep(falsen, ProofRule::EQ_RESOLVE, {inst, ief}, {});
  }
  cdp->addStep(qnorm.notNode(), ProofRule::SCOPE, {falsen}, {qnorm});
  Node qneqf = qnorm.eqNode(falsen);
  cdp->addStep(qneqf, ProofRule::FALSE_INTRO, {qnorm.notNode()}, {});
  Assert(eq[1] == falsen);
  if (!eqnorm.isNull())
  {
    cdp->addStep(eq, ProofRule::TRANS, {eqnorm, qneqf}, {});
  }
  else
  {
    Assert(qneqf == eq);
  }
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
    Assert(false) << "Unexpected input ensureProofMacroQuantMiniscope " << eq;
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
    Assert(false) << "Failed ensureProofMacroQuantMiniscope " << eq;
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
                           TConvPolicy::FIXPOINT,
                           TConvCachePolicy::NEVER,
                           "EnsureProofMacroQuantRewrite",
                           &wktc);
  theory::quantifiers::QuantifiersRewriter qrew(
      nodeManager(), d_env.getRewriter(), options());
  Node qr = qrew.computeRewriteBody(eq[0], &tcpg);
  if (qr != eq[1])
  {
    Assert(false) << "Failed to rewrite " << eq[0] << " to " << qr
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
  Node zero = theory::bv::utils::mkZero(nodeManager(), nsn.getType().getBitVectorSize());
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

bool BasicRewriteRCons::ensureProofMacroLambdaCaptureAvoid(CDProof* cdp,
                                                           const Node& eq)

{
  Trace("brc-macro") << "Expand macro lambda app elim shadow for " << eq
                     << std::endl;
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
  Assert(false);
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
  Assert(false);
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

Node BasicRewriteRCons::proveTransIneq(CDProof* cdp,
                                       const Node& leq1,
                                       const Node& leq2)
{
  Assert(leq1.getKind() == Kind::LEQ || leq1.getKind() == Kind::GEQ);
  Assert(leq1.getKind() == leq2.getKind());
  Assert(leq1[1] == leq2[0]);
  bool isLeq = leq1.getKind() == Kind::LEQ;
  NodeManager* nm = nodeManager();
  // always want this conclusion
  Node conc = nm->mkNode(leq1.getKind(), leq1[0], leq2[1]);
  // must flip
  Node leq1n = leq1;
  if (!isLeq)
  {
    leq1n = nm->mkNode(Kind::LEQ, leq1[1], leq1[0]);
    Node eq1 = leq1.eqNode(leq1n);
    cdp->addTrustedStep(
        eq1, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    cdp->addStep(leq1n, ProofRule::EQ_RESOLVE, {leq1, eq1}, {});
  }
  Node negOne = nm->mkConstRealOrInt(leq2[1].getType(), Rational(-1));
  Node leq2n = nm->mkNode(Kind::LEQ,
                          nm->mkNode(Kind::MULT, negOne, leq2[isLeq ? 1 : 0]),
                          nm->mkNode(Kind::MULT, negOne, leq2[isLeq ? 0 : 1]));
  Node eq2 = leq2.eqNode(leq2n);
  cdp->addTrustedStep(eq2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(leq2n, ProofRule::EQ_RESOLVE, {leq2, eq2}, {});

  // sum the inequalities
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node sumLeq = pc->checkDebug(ProofRule::ARITH_SUM_UB, {leq1n, leq2n}, {});
  Assert(!sumLeq.isNull());
  Assert(sumLeq != conc);
  cdp->addStep(sumLeq, ProofRule::ARITH_SUM_UB, {leq1n, leq2n}, {});

  Node eqc = sumLeq.eqNode(conc);
  cdp->addTrustedStep(eqc, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
  cdp->addStep(conc, ProofRule::EQ_RESOLVE, {sumLeq, eqc}, {});
  return conc;
}

bool BasicRewriteRCons::proveIneqWeaken(CDProof* cdp,
                                        const Node& src,
                                        const Node& tgt)
{
  Assert(src.getKind() == Kind::LEQ || src.getKind() == Kind::GEQ);
  NodeManager* nm = nodeManager();
  Node impl = nm->mkNode(Kind::IMPLIES, src, tgt);
  Trace("brc-macro") << "Prove: " << impl << std::endl;
  if (tgt.getKind() == Kind::LT || tgt.getKind() == Kind::GT)
  {
    // normalize the inequality
    Node srcn = src;
    if (src.getKind() == Kind::GEQ)
    {
      srcn = nm->mkNode(Kind::LEQ, src[1], src[0]);
      Node eq = src.eqNode(srcn);
      cdp->addTrustedStep(
          eq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      cdp->addStep(srcn, ProofRule::EQ_RESOLVE, {src, eq}, {});
    }
    TypeNode tn = srcn[0].getType();
    Node wineq = nm->mkNode(Kind::LT,
                            nm->mkConstRealOrInt(tn, Rational(0)),
                            nm->mkConstRealOrInt(tn, Rational(1)));
    cdp->addTrustedStep(
        wineq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
    Node sumLeq = pc->checkDebug(ProofRule::ARITH_SUM_UB, {srcn, wineq}, {});
    Assert(!sumLeq.isNull());
    cdp->addStep(sumLeq, ProofRule::ARITH_SUM_UB, {srcn, wineq}, {});
    impl = nm->mkNode(Kind::IMPLIES, sumLeq, tgt);
    Trace("brc-macro") << "Normalized prove: " << impl << std::endl;
    // should be equivalent
    Node eq = sumLeq.eqNode(tgt);
    cdp->addTrustedStep(eq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    cdp->addStep(tgt, ProofRule::EQ_RESOLVE, {sumLeq, eq}, {});
  }
  else if (tgt.getKind() == Kind::NOT && tgt[0].getKind() == Kind::EQUAL
           && tgt[0][0] == src[0])
  {
    CDProof cds(d_env);
    cds.addProof(cdp->getProofFor(src));
    Node srcc = nm->mkNode(src.getKind(), tgt[0][1], src[1]);
    Node equiv = src.eqNode(srcc);
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(src, cargs);
    Node ser1 = src[1].eqNode(src[1]);
    cds.addStep(ser1, ProofRule::REFL, {}, {src[1]});
    cds.addStep(equiv, cr, {tgt[0], ser1}, cargs);
    cds.addStep(srcc, ProofRule::EQ_RESOLVE, {src, equiv}, {});
    Trace("brc-macro") << "Substituted prove: " << srcc << std::endl;
    Node falsen = nm->mkConst(false);
    Node eqq = srcc.eqNode(falsen);
    cds.addTrustedStep(eqq, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    cds.addStep(falsen, ProofRule::EQ_RESOLVE, {srcc, eqq}, {});
    cds.addStep(tgt, ProofRule::SCOPE, {falsen}, {tgt[0]});

    Trace("brc-macro") << "Subproof " << *cds.getProofFor(tgt).get()
                       << std::endl;
    cdp->addProof(cds.getProofFor(tgt));
  }
  else
  {
    return false;
  }
  return true;
}

Node BasicRewriteRCons::proveGeneralReMembership(CDProof* cdp, const Node& n)
{
  NodeManager* nm = nodeManager();
  theory::strings::RegExpEntail re(nm, nullptr);
  Node gre = re.getGeneralizedConstRegExp(n);
  Assert(!gre.isNull());
  std::vector<Node> ncs, rcs;
  if (n.getKind() == Kind::STRING_CONCAT)
  {
    Assert(gre.getKind() == Kind::REGEXP_CONCAT);
    ncs.insert(ncs.end(), n.begin(), n.end());
    rcs.insert(rcs.end(), gre.begin(), gre.end());
  }
  else
  {
    ncs.push_back(n);
    rcs.push_back(gre);
  }
  Assert(ncs.size() == rcs.size());
  std::vector<Node> premises;
  for (size_t i = 0, nchild = rcs.size(); i < nchild; i++)
  {
    Node mem = nm->mkNode(Kind::STRING_IN_REGEXP, ncs[i], rcs[i]);
    cdp->addTrustedStep(mem, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    premises.push_back(mem);
  }
  if (premises.size() == 1)
  {
    return premises[0];
  }
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node memc = pc->checkDebug(ProofRule::RE_CONCAT, premises, {});
  cdp->addStep(memc, ProofRule::RE_CONCAT, premises, {});
  return memc;
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
      // Theory rewrites may require macro expansion
      ensureProofForTheoryRewrite(cdp, prid, eq);
      return true;
    }
  }
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "rewriter/basic_rewrite_rcons.h"

#include "expr/nary_term_util.h"
#include "expr/node_algorithm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "rewriter/rewrite_db_term_process.h"
#include "rewriter/rewrites.h"
#include "smt/env.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_proof_utilities.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "theory/strings/strings_entail.h"
#include "theory/strings/theory_strings_utils.h"
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

BasicRewriteRCons::BasicRewriteRCons(Env& env) : EnvObj(env)
{

}

bool BasicRewriteRCons::prove(CDProof* cdp,
                              Node a,
                              Node b,
                              std::vector<std::shared_ptr<ProofNode>>& subgoals,
                              TheoryRewriteMode tmode)
{
  Node eq = a.eqNode(b);
  Trace("trewrite-rcons") << "Reconstruct " << eq << std::endl;
  Node lhs = eq[0];
  Node rhs = eq[1];
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

  // try theory rewrite (pre-rare)
  if (tmode == TheoryRewriteMode::STANDARD)
  {
    if (tryTheoryRewrite(cdp, eq, theory::TheoryRewriteCtx::PRE_DSL, subgoals))
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
    std::vector<std::shared_ptr<ProofNode>>& subgoals,
    TheoryRewriteMode tmode)
{
  Node eq = a.eqNode(b);
  // try theory rewrite (post-rare), which may try both pre and post if
  // the proof-granularity mode is dsl-rewrite-strict.
  bool success = false;
  if (tmode == TheoryRewriteMode::RESORT)
  {
    if (tryTheoryRewrite(cdp, eq, theory::TheoryRewriteCtx::PRE_DSL, subgoals))
    {
      success = true;
    }
  }
  if (!success && tmode != TheoryRewriteMode::NEVER
      && tryTheoryRewrite(
          cdp, eq, theory::TheoryRewriteCtx::POST_DSL, subgoals))
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

void BasicRewriteRCons::ensureProofForTheoryRewrite(
    CDProof* cdp,
    ProofRewriteRule id,
    const Node& eq,
    std::vector<std::shared_ptr<ProofNode>>& subgoals)
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
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
      if (ensureProofMacroArithStringPredEntail(cdp, eq))
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
    default: break;
  }
  if (handledMacro)
  {
    std::shared_ptr<ProofNode> pfn = cdp->getProofFor(eq);
    Trace("brc-macro") << "...proof is " << *pfn.get() << std::endl;
    expr::getSubproofRule(pfn, ProofRule::TRUST, subgoals);
    return;
  }
  // default, just add the rewrite
  std::vector<Node> args;
  args.push_back(
      nodeManager()->mkConstInt(Rational(static_cast<uint32_t>(id))));
  args.push_back(eq);
  cdp->addStep(eq, ProofRule::THEORY_REWRITE, {}, args);
}

bool BasicRewriteRCons::ensureProofMacroBoolNnfNorm(CDProof* cdp,
                                                    const Node& eq)
{
  Trace("brc-macro") << "Expand Bool NNF norm " << eq[0] << " == " << eq[1]
                     << std::endl;
  // Call the utility again with proof tracking and construct the term
  // conversion proof. This proof itself may have trust steps in it.
  TConvProofGenerator tcpg(d_env, nullptr);
  Node nr = theory::booleans::TheoryBoolRewriter::computeNnfNorm(
      nodeManager(), eq[0], &tcpg);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(eq);
  Trace("brc-macro") << "...proof is " << *pfn.get() << std::endl;
  cdp->addProof(pfn);
  return true;
}

bool BasicRewriteRCons::ensureProofMacroArithStringPredEntail(CDProof* cdp,
                                                              const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("brc-macro") << "Expand entailment for " << eq << std::endl;
  theory::strings::ArithEntail ae(nullptr);
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
  Node ev = evaluate(approxRewGeq, {}, {});
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
    Node sumBound = theory::arith::expandMacroSumUb(children, args, cdp);
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
  theory::strings::ArithEntail ae(nullptr);
  theory::strings::StringsEntail sent(nullptr, ae, nullptr);
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
  // via ProofRewriteRule::QUANT_MINISCOPE_FV.
  if (!cdp->addTheoryRewriteStep(eqq2, ProofRewriteRule::QUANT_MINISCOPE_FV))
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
  if (!qrew.getVarElim(q[1], args, vars, subs, lits))
  {
    return false;
  }
  if (args.size() != q[0].getNumChildren() - 1)
  {
    // a rare case of MACRO_QUANT_VAR_ELIM_EQ does "datatype tester expansion"
    // e.g. forall x. is-cons(x) => P(x) ----> forall yz. P(cons(y,z))
    // This is not handled currently.
    return false;
  }
  Assert(vars.size() == 1);
  Trace("brc-macro") << "Ensure quant var elim eq: " << eq << std::endl;
  Trace("brc-macro") << "Eliminate " << vars << " -> " << subs << " from "
                     << lits << std::endl;
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
    std::vector<Node> cprems;
    for (size_t i = 0, nchild = body1r.getNumChildren(); i < nchild; i++)
    {
      Node eql = body1r[i].eqNode(body1re[i]);
      if (body1r[i] == body1re[i])
      {
        cdp->addStep(eql, ProofRule::REFL, {}, {eql[0]});
      }
      else
      {
        cdp->addTrustedStep(
            eql, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      }
      cprems.emplace_back(eql);
    }
    std::vector<Node> cargs;
    ProofRule cr = expr::getCongRule(body1r, cargs);
    Node eqbr = body1r.eqNode(body1re);
    cdp->addStep(eqbr, cr, cprems, cargs);
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
  if (!cdp->addStep(premise, ProofRule::ARITH_POLY_NORM, {}, {premise}))
  {
    Trace("brc-macro") << "...fail premise" << std::endl;
    return false;
  }
  Node kn = ProofRuleChecker::mkKindNode(eq[0].getKind());
  if (!cdp->addStep(eq, ProofRule::ARITH_POLY_NORM_REL, {premise}, {kn}))
  {
    Trace("brc-macro") << "...fail application" << std::endl;
    return false;
  }
  return true;
}

bool BasicRewriteRCons::tryTheoryRewrite(
    CDProof* cdp,
    const Node& eq,
    theory::TheoryRewriteCtx ctx,
    std::vector<std::shared_ptr<ProofNode>>& subgoals)
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
                {mkRewriteRuleNode(prid), eq},
                false))
    {
      // Theory rewrites may require macro expansion
      ensureProofForTheoryRewrite(cdp, prid, eq, subgoals);
      return true;
    }
  }
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal

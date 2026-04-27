/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for elaborating MACRO_STR_* and related string proof rewrites.
 */

#include "theory/strings/macro_rewrite_elaborator.h"

#include <algorithm>
#include <map>

#include "expr/aci_norm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "rewriter/rewrite_db_term_process.h"
#include "smt/env.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_proof_utilities.h"
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
namespace theory {
namespace strings {

MacroRewriteElaborator::MacroRewriteElaborator(Env& env) : EnvObj(env) {}
MacroRewriteElaborator::~MacroRewriteElaborator() {}

bool MacroRewriteElaborator::ensureProofFor(CDProof* cdp,
                                            ProofRewriteRule id,
                                            const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("str-rew-elab") << "ensureProofFor: " << id << " " << eq << std::endl;
  switch (id)
  {
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
      return ensureProofForArithStringPredEntail(cdp, eq);
    case ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION:
      return ensureProofForReInterUnionInclusion(cdp, eq);
    case ProofRewriteRule::MACRO_RE_INTER_UNION_CONST_ELIM:
      return ensureProofForReInterUnionConstElim(cdp, eq);
    case ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH:
      return ensureProofForSubstrStripSymLength(cdp, eq);
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY_PREFIX:
      return ensureProofForStrEqLenUnifyPrefix(cdp, eq);
    case ProofRewriteRule::MACRO_STR_EQ_LEN_UNIFY:
      return ensureProofForStrEqLenUnify(cdp, eq);
    case ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS:
    case ProofRewriteRule::MACRO_STR_SPLIT_CTN:
      return ensureProofForOverlap(id, cdp, eq);
    case ProofRewriteRule::MACRO_STR_COMPONENT_CTN:
      return ensureProofForStrComponentCtn(cdp, eq);
    case ProofRewriteRule::MACRO_STR_CONST_NCTN_CONCAT:
      return ensureProofForStrConstNCtnConcat(cdp, eq);
    case ProofRewriteRule::MACRO_STR_IN_RE_INCLUSION:
      return ensureProofForStrInReInclusion(cdp, eq);
    default: break;
  }
  return false;
}

bool MacroRewriteElaborator::ensureProofForArithStringPredEntail(CDProof* cdp,
                                                                 const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("brc-macro") << "Expand entailment for " << eq << std::endl;
  ArithEntail ae(nodeManager(), nullptr);
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
    DebugUnhandled();
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
    if (!ensureProofForArithPolyNormRel(cdp, areq))
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      DebugUnhandled();
      return false;
    }
    transEq.push_back(areq);
  }
  Node teq = approxRewGeq.eqNode(truen);
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
  if (transEq.size() > 1)
  {
    teq = geq.eqNode(truen);
    cdp->addStep(teq, ProofRule::TRANS, transEq, {});
  }

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
      DebugUnhandled();
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
      DebugUnhandled();
      return false;
    }
    Node cpred = nodeManager()->mkNode(
        sumBound.getKind(), nodeManager()->mkConstInt(pyr), zero);
    Node peq = sumBound.eqNode(cpred);
    if (!ensureProofForArithPolyNormRel(cdp, peq))
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      DebugUnhandled();
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
    Node peq = lhs.eqNode(geq);
    if (!ensureProofForArithPolyNormRel(cdp, peq))
    {
      Trace("brc-macro") << "...failed to show normalization (true case) "
                         << lhs << " and " << geq << std::endl;
      DebugUnhandled();
      return false;
    }
    cdp->addStep(eqii, ProofRule::TRANS, {peq, teq}, {});
  }
  Trace("brc-macro") << "...success" << std::endl;
  return true;
}

bool MacroRewriteElaborator::ensureProofForReInterUnionInclusion(CDProof* cdp,
                                                                 const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand re inter union inclusion " << eq << std::endl;
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
    rem.insert(rem.end(), eq[1].begin() + 1, eq[1].end());
  }
  else
  {
    diff.insert(diff.end(), eq[0].begin(), eq[0].end());
  }
  if (diff.size() != 2)
  {
    Trace("brc-macro") << "...fail diff " << diff << std::endl;
    DebugUnhandled();
    return false;
  }
  if (diff[0].getKind() == Kind::REGEXP_COMPLEMENT)
  {
    Node tmp = diff[0];
    diff[0] = diff[1];
    diff[1] = tmp;
  }
  Node d = nm->mkNode(k, diff);
  Trace("brc-macro") << "...input difference " << d << std::endl;
  ProofRewriteRule rule = k == Kind::REGEXP_INTER
                              ? ProofRewriteRule::RE_INTER_INCLUSION
                              : ProofRewriteRule::RE_UNION_INCLUSION;
  theory::Rewriter* rr = d_env.getRewriter();
  Node ret = rr->rewriteViaRule(rule, d);
  if (ret.isNull() || (ret != eq[1] && ret != eq[1][0]))
  {
    Trace("brc-macro") << "...fail target " << ret << std::endl;
    DebugUnhandled();
    return false;
  }
  Node equiv = d.eqNode(ret);
  Trace("brc-macro") << "... successfully proven " << equiv << std::endl;
  cdp->addTheoryRewriteStep(equiv, rule);
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
      DebugUnhandled();
      return false;
    }
    Trace("brc-macro") << "...aci norm " << eqa << std::endl;
    transEq.push_back(eqa);
  }
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
    Node rkret = nm->mkNode(k, ret, r[1]);
    Node rret = r.eqNode(rkret);
    cdp->addStep(rret, cr, {equiv, refl}, cargs);
    transEq.push_back(rret);
    if (rkret!=eq[1])
    {
      Node eqt = rkret.eqNode(eq[1]);
      Trace("brc-macro") << "... subgoal " << eqt << std::endl;
      cdp->addTrustedStep(eqt, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
      transEq.push_back(eqt);
    }
  }
  cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  return true;
}

bool MacroRewriteElaborator::ensureProofForReInterUnionConstElim(CDProof* cdp,
                                                                 const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand macro re inter union const elim for " << eq
                     << std::endl;
  if (eq[0].getKind() == Kind::REGEXP_INTER)
  {
    ArithEntail ae(nm, nullptr);
    StringsEntail se(nullptr, ae);
    SequencesRewriter srew(nm, ae, se, nullptr);
    Node tgt;
    Node res = srew.rewriteViaMacroReInterUnionConstElim(eq[0], tgt);
    if (eq[1].getKind() == Kind::STRING_TO_REGEXP)
    {
      tgt = eq[1];
    }
    else
    {
      Assert(eq[1].getKind() == Kind::REGEXP_NONE && !tgt.isNull());
    }
    Trace("brc-macro") << "...target is " << tgt << std::endl;
    if (!tgt.isNull() && tgt != eq[0][0])
    {
      std::vector<Node> newChildren;
      newChildren.push_back(tgt);
      newChildren.insert(newChildren.end(), eq[0].begin(), eq[0].end());
      Node rnew = nm->mkNode(Kind::REGEXP_INTER, newChildren);
      Node eq1 = eq[0].eqNode(rnew);
      Node eq2 = rnew.eqNode(eq[1]);
      Trace("brc-macro") << "...decompose to " << eq1 << ", " << eq2
                         << std::endl;
      cdp->addStep(eq1, ProofRule::ACI_NORM, {}, {eq1});
      cdp->addTrustedStep(eq2, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
      cdp->addStep(eq, ProofRule::TRANS, {eq1, eq2}, {});
    }
    else
    {
      cdp->addTrustedStep(eq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    }
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
  for (size_t i = 0, ndiff = diff.size(); i < ndiff; i++)
  {
    size_t ii = ndiff - i - 1;
    Node next = nm->mkNode(Kind::REGEXP_UNION, diff[ii], curr);
    Node eqc = next.eqNode(curr);
    cdp->addTrustedStep(eqc, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
    transEq.push_back(eqc);
    curr = next;
  }
  if (eq[0] != curr)
  {
    Node eqa = eq[0].eqNode(curr);
    if (!cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa}))
    {
      DebugUnhandled();
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

bool MacroRewriteElaborator::ensureProofForSubstrStripSymLength(CDProof* cdp,
                                                                const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand substring strip for " << eq << std::endl;
  Assert(eq.getKind() == Kind::EQUAL);
  Node lhs = eq[0];
  Assert(lhs.getKind() == Kind::STRING_SUBSTR);
  Rewrite rule;
  ArithEntail ae(nm, nullptr);
  StringsEntail sent(nullptr, ae);
  std::vector<Node> ch1;
  std::vector<Node> ch2;
  Node rhs = sent.rewriteViaMacroSubstrStripSymLength(lhs, rule, ch1, ch2);
  Trace("brc-macro") << "...was via string rewrite rule " << rule << std::endl;
  Assert(rhs == eq[1]);
  TypeNode stype = lhs.getType();
  Node cm1 = utils::mkConcat(ch1, stype);
  Node cm2 = utils::mkConcat(ch2, stype);
  Node cm;
  if (rule == Rewrite::SS_STRIP_END_PT)
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
  if (expr::isACINorm(lhs[0], cm))
  {
    cdp->addStep(eq1, ProofRule::ACI_NORM, {}, {eq1});
    Trace("brc-macro") << "- via ACI_NORM " << eq1 << std::endl;
  }
  else
  {
    rewriter::RewriteDbNodeConverter rdnc(nodeManager());
    Node eq1t = rdnc.convert(eq1);
    Assert(eq1t.getKind() == Kind::EQUAL);
    if (eq1t[0] != eq1t[1])
    {
      return false;
    }
    ensureProofForEncodeTransform(cdp, eq1, eq1t);
    Node equivs = eq1t.eqNode(eq1);
    cdp->addStep(equivs, ProofRule::SYMM, {eq1.eqNode(eq1t)}, {});
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
  cdp->addTrustedStep(eqm, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  Trace("brc-macro") << "- rely on rewrite " << eqm << std::endl;
  cdp->addStep(eq, ProofRule::TRANS, {eqLhs, eqm}, {});
  return true;
}

bool MacroRewriteElaborator::ensureProofForStrEqLenUnifyPrefix(CDProof* cdp,
                                                               const Node& eq)
{
  Trace("brc-macro") << "Expand macro str eq len unify prefix " << eq
                     << std::endl;
  NodeManager* nm = nodeManager();
  ArithEntail ae(nm, nullptr);
  StringsEntail sent(nullptr, ae);

  Assert(eq[1].getKind() == Kind::AND);
  Node eq1p = eq[1];
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
  Node leneq = expr::proveCong(d_env, &cdfwd, len1, {eqsrc});
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
    Node equiv = expr::proveCong(d_env, &cdfwd, leneq, eqi);
    cdfwd.addStep(leneqi, ProofRule::EQ_RESOLVE, {leneq, equiv}, {});
  }
  Trace("brc-macro") << "...length: " << li[0] << " == " << li[1] << std::endl;
  Node diff = nm->mkNode(Kind::SUB, li[1], li[0]);
  Node diffn = theory::arith::PolyNorm::getPolyNorm(diff);
  Trace("brc-macro") << "...norm diff " << diffn << std::endl;
  Node diffneqz = diffn.eqNode(nm->mkConstInt(Rational(0)));
  Node equiv = leneqi.eqNode(diffneqz);
  if (!ensureProofForArithPolyNormRel(&cdfwd, equiv))
  {
    Trace("brc-macro") << "... failed poly norm rel" << std::endl;
    return false;
  }
  cdfwd.addStep(diffneqz, ProofRule::EQ_RESOLVE, {leneqi, equiv}, {});
  Trace("brc-macro") << "...have " << diffneqz << std::endl;

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
  Node cc = utils::mkConcat(concat, stype);
  Node lcc = nm->mkNode(Kind::STRING_LENGTH, cc);
  TConvProofGenerator tcpg(d_env, nullptr);
  Node lcci = ae.rewriteLengthIntro(lcc, &tcpg);
  Trace("brc-macro") << "...normalized concat length " << lcci << std::endl;
  Node lcceq = lcc.eqNode(lcci);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(lcceq);
  cdfwd.addProof(pfn);

  Node pnEq = lcci.eqNode(diffneqz[0]);
  if (!cdfwd.addStep(pnEq, ProofRule::ARITH_POLY_NORM, {}, {pnEq}))
  {
    Trace("brc-macro") << "...fail poly norm " << pnEq << std::endl;
    return false;
  }
  Node pnEq2 = lcc.eqNode(diffneqz[1]);
  cdfwd.addStep(pnEq2, ProofRule::TRANS, {lcceq, pnEq, diffneqz}, {});
  Trace("brc-macro") << "...have " << pnEq2 << std::endl;
  Node eqconv = pnEq2.eqNode(eq1p[1]);
  Trace("brc-macro") << "- subgoal " << eqconv << std::endl;
  cdfwd.addTrustedStep(eqconv, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdfwd.addStep(eq1p[1], ProofRule::EQ_RESOLVE, {pnEq2, eqconv}, {});

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
  Node cres = expr::proveCong(d_env, &cdmid, srcRew, eqe);
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

  cdfwd.addProof(pfmid);
  cdfwd.addStep(implMid[1], ProofRule::MODUS_PONENS, {eq1p[1], implMid}, {});
  cdfwd.addStep(eq1p[0], ProofRule::EQ_RESOLVE, {eq[0], implMid[1]}, {});
  cdfwd.addStep(eq1p, ProofRule::AND_INTRO, {eq1p[0], eq1p[1]}, {});
  Node impl = nm->mkNode(Kind::IMPLIES, eq[0], eq1p);
  cdfwd.addStep(impl, ProofRule::SCOPE, {eq1p}, {eq[0]});
  cdp->addProof(cdfwd.getProofFor(impl));

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

  Node eqfinal = proveDualImplication(cdp, impl, implrev);

  if (eq1p != eq[1])
  {
    cdp->addStep(eq, ProofRule::TRANS, {eqfinal, eq1p.eqNode(eq[1])}, {});
  }

  return true;
}

bool MacroRewriteElaborator::ensureProofForStrEqLenUnify(CDProof* cdp,
                                                         const Node& eq)
{
  NodeManager* nm = nodeManager();
  Trace("brc-macro") << "Expand macro str eq len unify for " << eq << std::endl;
  Assert(eq[1].getKind() == Kind::AND && eq[1].getNumChildren() == 2);
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
  CDProof cdfwd(d_env);
  Node clhs = nm->mkNode(Kind::STRING_CONCAT, elhs);
  Node crhs = nm->mkNode(Kind::STRING_CONCAT, erhs);
  Node ceq = clhs.eqNode(crhs);

  Node llhs0 = nm->mkNode(Kind::STRING_LENGTH, elhs[0]);
  Node lrhs0 = nm->mkNode(Kind::STRING_LENGTH, erhs[0]);
  Node leq = llhs0.eqNode(lrhs0);
  Trace("brc-macro") << "- subgoal " << leq << std::endl;
  cdfwd.addTrustedStep(leq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
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
  cdfwd.addStep(cpremises[1], ProofRule::CONCAT_EQ, {equiv2}, {falsen});
  cdfwd.addStep(eq[1], ProofRule::AND_INTRO, cpremises, {});
  Node impl = nm->mkNode(Kind::IMPLIES, ceq, eq[1]);
  cdfwd.addStep(impl, ProofRule::SCOPE, {eq[1]}, {ceq});
  cdp->addProof(cdfwd.getProofFor(impl));

  CDProof cdrev(d_env);
  cdrev.addStep(
      cpremises[0], ProofRule::AND_ELIM, {eq[1]}, {nm->mkConstInt(0)});
  cdrev.addStep(
      cpremises[1], ProofRule::AND_ELIM, {eq[1]}, {nm->mkConstInt(1)});
  cargs.clear();
  ccr = expr::getCongRule(ceq[0], cargs);
  cdrev.addStep(ceq, ccr, cpremises, cargs);
  Node implrev = nm->mkNode(Kind::IMPLIES, eq[1], ceq);
  cdrev.addStep(implrev, ProofRule::SCOPE, {ceq}, {eq[1]});
  cdp->addProof(cdrev.getProofFor(implrev));

  Node eqfinal = proveDualImplication(cdp, impl, implrev);

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

bool MacroRewriteElaborator::ensureProofForOverlap(ProofRewriteRule id,
                                                   CDProof* cdp,
                                                   const Node& eq)
{
  Trace("brc-macro") << "Expand macro overlap (" << id << ") for " << eq
                     << std::endl;
  NodeManager* nm = nodeManager();
  Assert(eq[0].getNumChildren() >= 2);
  Node concat = eq[0][0];
  TypeNode stype = concat.getType();
  Node emp = Word::mkEmptyWord(stype);
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
    std::vector<Node> childpre(concat.begin(), concat.begin() + nchildpre);
    Node cpre = utils::mkConcat(childpre, stype);
    Node cmid = concat[nchildpre];
    std::vector<Node> childpost(concat.begin() + nchildpre + 1, concat.end());
    Node cpost = utils::mkConcat(childpost, stype);
    Node cgroup = nm->mkNode(Kind::STRING_CONCAT, cpre, cmid, cpost);
    if (concat != cgroup)
    {
      Node eqc = concat.eqNode(cgroup);
      if (!cdp->addStep(eqc, ProofRule::ACI_NORM, {}, {eqc}))
      {
        DebugUnhandled();
        return false;
      }
      premises.push_back(eqc);
    }
  }
  else
  {
    Assert(id == ProofRewriteRule::MACRO_STR_STRIP_ENDPOINTS);
    ArithEntail ae(nm, nullptr);
    StringsEntail se(nullptr, ae);
    SequencesRewriter srew(nm, ae, se, nullptr);
    std::vector<Node> nb, nc1, ne;
    Kind k = eq[0].getKind();
    Node res = srew.rewriteViaMacroStrStripEndpoints(eq[0], nb, nc1, ne);
    if (res != eq[1])
    {
      DebugUnhandled();
      return false;
    }
    std::vector<Node> nc2;
    utils::getConcat(eq[0][1], nc2);
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
        DebugUnhandled();
        return false;
      }
      newChildren[0].push_back(vec[0]);
      Assert(!nc2.empty());
      size_t index2 = i == 0 ? 0 : nc2.size() - 1;
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
    newChildren[0][remIndex] = utils::mkConcat(nc1, stype);
    newChildren[1][remIndex] = utils::mkConcat(nc2, stype);
    Trace("brc-macro") << "First child processed to : " << eq[0][0]
                       << " == " << newChildren[0] << std::endl;
    Trace("brc-macro") << "Second child processed to : " << eq[0][1]
                       << " == " << newChildren[1] << std::endl;
    Node g1 = utils::mkConcat(newChildren[0], stype);
    Node g2 = utils::mkConcat(newChildren[1], stype);
    if (g1 != eq[0][0])
    {
      Node eqc = eq[0][0].eqNode(g1);
      cdp->addTrustedStep(
          eqc, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
      premises.push_back(eqc);
    }
    if (g2 != eq[0][1])
    {
      if (g1 == eq[0][0])
      {
        Node refl = eq[0][0].eqNode(eq[0][0]);
        cdp->addStep(refl, ProofRule::REFL, {}, {eq[0][0]});
        premises.push_back(refl);
      }
      Node eqc = eq[0][1].eqNode(g2);
      if (!cdp->addStep(eqc, ProofRule::ACI_NORM, {}, {eqc}))
      {
        DebugUnhandled();
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
  Node input = eq[0];
  std::vector<Node> transEq;
  if (!premises.empty())
  {
    Node ceq = expr::proveCong(d_env, cdp, input, premises);
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
  Node equiv = input.eqNode(ret);
  cdp->addTheoryRewriteStep(equiv, rule);
  transEq.push_back(equiv);
  if (ret != eq[1])
  {
    Node eqpost = ret.eqNode(eq[1]);
    Trace("brc-macro") << "- post-process subgoal " << eqpost << std::endl;
    cdp->addTrustedStep(
        eqpost, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});
    transEq.push_back(eqpost);
  }
  if (transEq.size() > 1)
  {
    cdp->addStep(eq, ProofRule::TRANS, transEq, {});
  }
  return true;
}

bool MacroRewriteElaborator::ensureProofForStrComponentCtn(CDProof* cdp,
                                                           const Node& eq)
{
  Trace("brc-macro") << "Expand macro str component ctn " << eq << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_CONTAINS);
  ArithEntail ae(nodeManager(), nullptr);
  StringsEntail se(nullptr, ae);
  std::vector<Node> nc1, nc2;
  utils::getConcat(eq[0][0], nc1);
  utils::getConcat(eq[0][1], nc2);
  std::vector<Node> nc1rb, nc1re;
  if (se.componentContains(nc1, nc2, nc1rb, nc1re, true) == -1)
  {
    return false;
  }
  Trace("brc-macro") << "...partitioned to " << nc1rb << " " << nc1 << " "
                     << nc1re << std::endl;
  TypeNode stype = eq[0][0].getType();
  NodeManager* nm = nodeManager();
  std::vector<Node> cc;
  if (!nc1rb.empty())
  {
    cc.push_back(utils::mkConcat(nc1rb, stype));
  }
  if (!nc1.empty())
  {
    cc.push_back(utils::mkConcat(nc1, stype));
  }
  if (!nc1re.empty())
  {
    cc.push_back(utils::mkConcat(nc1re, stype));
  }
  Node cg = utils::mkConcat(cc, stype);
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

bool MacroRewriteElaborator::ensureProofForStrConstNCtnConcat(CDProof* cdp,
                                                              const Node& eq)
{
  Trace("brc-macro") << "Expand macro str const nctn concat " << eq
                     << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_CONTAINS);
  NodeManager* nm = nodeManager();
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node er = pc->checkDebug(ProofRule::STRING_EAGER_REDUCTION, {}, {eq[0]});
  Assert(!er.isNull());
  cdp->addStep(er, ProofRule::STRING_EAGER_REDUCTION, {}, {eq[0]});
  Trace("brc-macro") << "...eager reduce: " << er << std::endl;
  Node truen = nm->mkConst(true);
  Node eqt = eq[0].eqNode(truen);
  cdp->addStep(eqt, ProofRule::TRUE_INTRO, {eq[0]}, {});
  Node eqi = expr::proveCong(d_env, cdp, er, {eqt});
  if (eqi.isNull())
  {
    Trace("brc-macro") << "...failed cong" << std::endl;
    DebugUnhandled();
    return false;
  }
  Trace("brc-macro") << "...cong " << eqi << std::endl;
  AlwaysAssert(eqi[1].getKind() == Kind::ITE);
  Node eqi2 = eqi[1].eqNode(eqi[1][1]);
  cdp->addTrustedStep(eqi2, TrustId::MACRO_THEORY_REWRITE_RCONS_SIMPLE, {}, {});

  Node ere = er.eqNode(eqi[1][1]);
  cdp->addStep(ere, ProofRule::TRANS, {eqi, eqi2}, {});
  cdp->addStep(eqi[1][1], ProofRule::EQ_RESOLVE, {er, ere}, {});

  Node concat = eqi[1][1][1];
  AlwaysAssert(concat.getKind() == Kind::STRING_CONCAT
               && concat.getNumChildren() == 3);
  Node cf = concat;
  Node eqsf = eqi[1][1];
  if (concat[1].getKind() == Kind::STRING_CONCAT)
  {
    std::vector<Node> cc;
    cc.push_back(concat[0]);
    cc.insert(cc.end(), concat[1].begin(), concat[1].end());
    cc.push_back(concat[2]);
    cf = nm->mkNode(Kind::STRING_CONCAT, cc);
    Node eqa = concat.eqNode(cf);
    if (!cdp->addStep(eqa, ProofRule::ACI_NORM, {}, {eqa}))
    {
      Trace("brc-macro") << "...failed ACI" << std::endl;
      DebugUnhandled();
      return false;
    }
    eqsf = eqi[1][1][0].eqNode(cf);
    cdp->addStep(eqsf, ProofRule::TRANS, {eqi[1][1], eqa}, {});
  }
  Node eqsfs = proveSymm(cdp, eqsf);
  Trace("brc-macro") << "Have : " << eqsfs << std::endl;

  Node mem = proveGeneralReMembership(cdp, cf);
  Trace("brc-macro") << "Membership : " << mem << std::endl;

  Node memc = expr::proveCong(d_env, cdp, mem, {eqsfs});
  Trace("brc-macro") << "Cong membership : " << memc << std::endl;

  theory::Rewriter* rr = d_env.getRewriter();
  Node res = rr->rewriteViaRule(ProofRewriteRule::STR_IN_RE_EVAL, memc[1]);
  if (res.isNull() || res != eq[1])
  {
    Trace("brc-macro") << "...failed str in eval" << std::endl;
    DebugUnhandled();
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

bool MacroRewriteElaborator::ensureProofForStrInReInclusion(CDProof* cdp,
                                                            const Node& eq)
{
  Trace("brc-macro") << "Expand macro str in re inclusion for " << eq
                     << std::endl;
  Assert(eq[0].getKind() == Kind::STRING_IN_REGEXP);
  NodeManager* nm = nodeManager();
  Node truen = eq[1];
  Assert(truen.isConst() && truen.getConst<bool>());

  Node trivMemc = proveGeneralReMembership(cdp, eq[0][0]);
  Trace("brc-macro") << "Trivial membership: " << trivMemc << std::endl;

  Node comp = nm->mkNode(Kind::REGEXP_COMPLEMENT, eq[0][1]);
  Node inter = nm->mkNode(Kind::REGEXP_INTER, trivMemc[1], comp);
  Trace("brc-macro") << "Rewrite inclusion: " << inter << std::endl;
  theory::Rewriter* rr = d_env.getRewriter();
  Node res = rr->rewriteViaRule(ProofRewriteRule::RE_INTER_INCLUSION, inter);
  Trace("brc-macro") << "...returned " << res << std::endl;
  if (res.isNull())
  {
    DebugUnhandled();
    return false;
  }
  Node inclusionEq = inter.eqNode(res);
  cdp->addTheoryRewriteStep(inclusionEq, ProofRewriteRule::RE_INTER_INCLUSION);

  Node memNeg = eq[0].notNode();
  Node memComp = nm->mkNode(Kind::STRING_IN_REGEXP, eq[0][0], comp);
  Node compEq = memNeg.eqNode(memComp);
  cdp->addTrustedStep(compEq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdp->addStep(memComp, ProofRule::EQ_RESOLVE, {memNeg, compEq}, {});

  Node imem = nm->mkNode(Kind::STRING_IN_REGEXP, eq[0][0], inter);
  cdp->addStep(imem, ProofRule::RE_INTER, {trivMemc, memComp}, {});

  Node meq = expr::proveCong(d_env, cdp, imem, {Node::null(), inclusionEq});
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

void MacroRewriteElaborator::ensureProofForEncodeTransform(CDProof* cdp,
                                                           const Node& eq,
                                                           const Node& eqi)
{
  rewriter::ProofRewriteDbNodeConverter rdnc(d_env);
  std::shared_ptr<ProofNode> pfn = rdnc.convert(eq);
  Node equiv = eq.eqNode(eqi);
  Assert(pfn->getResult() == equiv);
  cdp->addProof(pfn);
  Node equivs = eqi.eqNode(eq);
  cdp->addStep(equivs, ProofRule::SYMM, {equiv}, {});
  cdp->addStep(eq, ProofRule::EQ_RESOLVE, {eqi, equivs}, {});
}

bool MacroRewriteElaborator::ensureProofForArithPolyNormRel(CDProof* cdp,
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

Node MacroRewriteElaborator::proveGeneralReMembership(CDProof* cdp,
                                                      const Node& n)
{
  Trace("brc-macro") << "proveGeneralReMembership " << n << std::endl;
  NodeManager* nm = nodeManager();
  RegExpEntail re(nm, nullptr);
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
    Trace("brc-macro") << "...returns (singleton) " << premises[0] << std::endl;
    return premises[0];
  }
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  Node memc = pc->checkDebug(ProofRule::RE_CONCAT, premises, {});
  Trace("brc-macro") << "...returns " << memc << " from " << premises
                     << std::endl;
  cdp->addStep(memc, ProofRule::RE_CONCAT, premises, {});
  return memc;
}

Node MacroRewriteElaborator::proveSymm(CDProof* cdp, const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Node eqs = eq[1].eqNode(eq[0]);
  cdp->addStep(eqs, ProofRule::SYMM, {eq}, {});
  return eqs;
}

Node MacroRewriteElaborator::proveDualImplication(CDProof* cdp,
                                                  const Node& impl,
                                                  const Node& implRev)
{
  Assert(impl.getKind() == Kind::IMPLIES && implRev.getKind() == Kind::IMPLIES
         && impl[0] == implRev[1] && impl[1] == implRev[0]);
  NodeManager* nm = nodeManager();
  Node dualImpl = nm->mkNode(Kind::AND, impl, implRev);
  cdp->addStep(dualImpl, ProofRule::AND_INTRO, {impl, implRev}, {});
  Node eqfinal = impl[0].eqNode(impl[1]);
  Node dualImplEq = nm->mkNode(Kind::EQUAL, dualImpl, eqfinal);
  Trace("brc-macro") << "- dual implication subgoal " << dualImplEq
                     << std::endl;
  cdp->addTrustedStep(dualImplEq, TrustId::MACRO_THEORY_REWRITE_RCONS, {}, {});
  cdp->addStep(eqfinal, ProofRule::EQ_RESOLVE, {dualImpl, dualImplEq}, {});
  return eqfinal;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

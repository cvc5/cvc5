/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
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
    case ProofRewriteRule::MACRO_SUBSTR_STRIP_SYM_LENGTH:
      if (ensureProofMacroSubstrStripSymLength(cdp, eq))
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

bool BasicRewriteRCons::ensureProofMacroSubstrStripSymLength(CDProof* cdp,
                                                             const Node& eq)
{
  NodeManager* nm = NodeManager::currentNM();
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

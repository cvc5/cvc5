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

#include "proof/proof_checker.h"
#include "proof/theory_rewrite_id.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

BasicRewriteRCons::BasicRewriteRCons(Env& env) : EnvObj(env) {}

bool BasicRewriteRCons::prove(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);
  Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << tid << ", "
                          << mid << ")" << std::endl;
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
  if (eq[0].getKind() == Kind::APPLY_UF
      && eq[0].getOperator().getKind() == Kind::LAMBDA)
  {
    std::vector<Node> args;
    args.push_back(eq[0].getOperator());
    args.insert(args.end(), eq[0].begin(), eq[0].end());
    if (tryRule(cdp, eq, ProofRule::BETA_REDUCE, args))
    {
      Trace("trewrite-rcons") << "...BETA_REDUCE" << std::endl;
      return true;
    }
  }
  if (tryRule(cdp, eq, ProofRule::EXISTS_ELIM, {eq[0]}))
  {
    Trace("trewrite-rcons") << "...EXISTS_ELIM" << std::endl;
    return true;
  }
  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}
bool BasicRewriteRCons::postProve(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);

  if (theory::TheoryId::THEORY_BV == tid)
  {
#define TRY_THEORY_REWRITE(id) \
    if (tryRule( \
            cdp, \
            eq, \
            ProofRule::THEORY_REWRITE, \
            {mkTheoryRewriteId(TheoryRewriteId::id), eq[0]})) \
    { \
      Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << tid \
                              << ", " << mid << ")" << std::endl; \
      return true; \
    } \
    /* end of macro */

    TRY_THEORY_REWRITE(BV_UMULO_ELIMINATE)
    TRY_THEORY_REWRITE(BV_SMULO_ELIMINATE)
    TRY_THEORY_REWRITE(BV_FLATTEN_ASSOC_COMMUTE)
    TRY_THEORY_REWRITE(BV_FLATTEN_ASSOC_COMMUTE_NO_DUPLICATES)
    TRY_THEORY_REWRITE(BV_ADD_COMBINE_LIKE_TERMS)
    TRY_THEORY_REWRITE(BV_MULT_SIMPLIFY)
    TRY_THEORY_REWRITE(BV_SOLVE_EQ)
    TRY_THEORY_REWRITE(BV_BITWISE_EQ)
    TRY_THEORY_REWRITE(BV_BITWISE_SLICING)
  }

  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::tryRule(CDProof* cdp,
                                Node eq,
                                ProofRule r,
                                const std::vector<Node>& args)
{
  Trace("trewrite-rcons-debug") << "Try " << r << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  // do not provide expected, as this will always succeed if proof checking
  // is disabled
  Node res = pc->checkDebug(r, {}, args, Node::null(), "trewrite-rcons");
  if (!res.isNull() && res == eq)
  {
    cdp->addStep(eq, r, {}, args);
    return true;
  }
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal

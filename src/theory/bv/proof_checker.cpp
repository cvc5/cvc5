/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vectors proof checker.
 */

#include "theory/bv/proof_checker.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "proof/theory_rewrite_id.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

void BVProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerTrustedChecker(ProofRule::MACRO_BV_BITBLAST, this, 2);
  pc->registerTrustedChecker(ProofRule::BV_BITBLAST_STEP, this, 2);
  pc->registerChecker(ProofRule::BV_EAGER_ATOM, this);
  pc->registerChecker(ProofRule::THEORY_REWRITE, this);
}

Node BVProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == ProofRule::MACRO_BV_BITBLAST)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_BITBLAST_STEP)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_EAGER_ATOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::BITVECTOR_EAGER_ATOM);
    return args[0].eqNode(args[0][0]);
  }
  else if (id == ProofRule::THEORY_REWRITE)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    TheoryRewriteId trid;
    if (!getTheoryRewriteId(args[0], trid)) {
      Unreachable();
    }

    auto const& node = args[1];
#define BV_PROOF_CASE(rule, name) \
    case TheoryRewriteId::rule: { \
      if (RewriteRule<name>::applies(node)) {                    \
      	return node.eqNode(RewriteRule<name>::run<false>(node)); \
      }                                                          \
      break;                                                     \
    }                                                            \
    /* end of macro */
    switch (trid) {
      BV_PROOF_CASE(BV_UMULO_ELIMINATE, UmuloEliminate)
      BV_PROOF_CASE(BV_SMULO_ELIMINATE, SmuloEliminate)
      BV_PROOF_CASE(BV_FLATTEN_ASSOC_COMMUTE, FlattenAssocCommut)
      BV_PROOF_CASE(BV_FLATTEN_ASSOC_COMMUTE_NO_DUPLICATES, FlattenAssocCommutNoDuplicates)
      BV_PROOF_CASE(BV_ADD_COMBINE_LIKE_TERMS, AddCombineLikeTerms)
      BV_PROOF_CASE(BV_MULT_SIMPLIFY, MultSimplify)
      BV_PROOF_CASE(BV_SOLVE_EQ, SolveEq)
      BV_PROOF_CASE(BV_BITWISE_EQ, BitwiseEq)
      BV_PROOF_CASE(BV_BITWISE_SLICING, BitwiseSlicing)
      default:
        Unreachable();
    }
  }

  return Node::null();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

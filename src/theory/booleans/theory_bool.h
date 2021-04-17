/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory of booleans.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BOOLEANS__THEORY_BOOL_H
#define CVC5__THEORY__BOOLEANS__THEORY_BOOL_H

#include "context/context.h"
#include "theory/booleans/proof_checker.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/theory.h"

namespace cvc5 {
namespace theory {
namespace booleans {

class TheoryBool : public Theory {
 public:
  TheoryBool(context::Context* c,
             context::UserContext* u,
             OutputChannel& out,
             Valuation valuation,
             const LogicInfo& logicInfo,
             ProofNodeManager* pnm = nullptr);

  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;

  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;

  std::string identify() const override;

 private:
  /** The theory rewriter for this theory. */
  TheoryBoolRewriter d_rewriter;
  /** Proof rule checker */
  BoolProofRuleChecker d_checker;
};/* class TheoryBool */

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BOOLEANS__THEORY_BOOL_H */

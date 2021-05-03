/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Built-in theory.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__THEORY_BUILTIN_H
#define CVC5__THEORY__BUILTIN__THEORY_BUILTIN_H

#include "theory/builtin/proof_checker.h"
#include "theory/builtin/theory_builtin_rewriter.h"
#include "theory/theory.h"

namespace cvc5 {
namespace theory {
namespace builtin {

class TheoryBuiltin : public Theory
{
 public:
  TheoryBuiltin(context::Context* c,
                context::UserContext* u,
                OutputChannel& out,
                Valuation valuation,
                const LogicInfo& logicInfo,
                ProofNodeManager* pnm = nullptr);

  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;

  std::string identify() const override;

  /** finish initialization */
  void finishInit() override;

 private:
  /** The theory rewriter for this theory. */
  TheoryBuiltinRewriter d_rewriter;
  /** Proof rule checker */
  BuiltinProofRuleChecker d_checker;
}; /* class TheoryBuiltin */

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BUILTIN__THEORY_BUILTIN_H */

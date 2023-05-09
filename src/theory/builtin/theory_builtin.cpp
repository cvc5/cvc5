/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the builtin theory.
 */

#include "theory/builtin/theory_builtin.h"

#include "expr/kind.h"
#include "proof/proof_node_manager.h"
#include "theory/builtin/theory_builtin_rewriter.h"
#include "theory/theory_model.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

TheoryBuiltin::TheoryBuiltin(Env& env, OutputChannel& out, Valuation valuation)
    : Theory(THEORY_BUILTIN, env, out, valuation),
      d_checker(env),
      d_state(env, valuation),
      d_im(env, *this, d_state, "theory::builtin::")
{
  // indicate we are using the default theory state and inference managers
  d_theoryState = &d_state;
  d_inferManager = &d_im;
}

TheoryRewriter* TheoryBuiltin::getTheoryRewriter() { return &d_rewriter; }

ProofRuleChecker* TheoryBuiltin::getProofChecker() { return &d_checker; }

std::string TheoryBuiltin::identify() const
{
  return std::string("TheoryBuiltin");
}

void TheoryBuiltin::finishInit()
{
  // Notice that choice is an unevaluated kind belonging to this theory.
  // However, it should be set as an unevaluated kind where it is used, e.g.
  // in the quantifiers theory. This ensures that a logic like QF_LIA, which
  // includes the builtin theory, does not mark any kinds as unevaluated and
  // hence it is easy to check for illegal eliminations via TheoryModel
  // (see TheoryModel::isLegalElimination) since there are no unevaluated kinds
  // present.
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

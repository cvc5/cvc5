
#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_EVALUATOR_H
#define CVC5__THEORY__ARITH__ARITH_EVALUATOR_H

#include <optional>

#include "expr/node.h"
#include "smt/env.h"

namespace cvc5 {
namespace theory {
namespace arith {

/**
 * Check if the expression `expr` is zero over the given model.
 * The model may contain real algebraic numbers in standard witness form.
 * The environment is used for rewriting.
 *
 * The result is true or false, if the expression could be evaluated. If it
 * could not, possibly in the presence of a transcendental model, the result is
 * std::nullopt.
 */
std::optional<bool> isExpressionZero(Env& env,
                                     Node expr,
                                     const std::map<Node, Node>& model);
}
}  // namespace theory
}  // namespace cvc5

#endif

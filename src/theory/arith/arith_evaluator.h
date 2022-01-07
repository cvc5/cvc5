
#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_EVALUATOR_H
#define CVC5__THEORY__ARITH__ARITH_EVALUATOR_H

#include "expr/node.h"
#include "smt/env.h"

namespace cvc5 {
namespace theory {
namespace arith {

/**
 * Check if the expression `expr` is zero over the given model.
 * The model may contain real algebraic numbers in standard witness form.
 * The environment is used for rewriting.
 */
bool isExpressionZero(Env& env, Node expr, const std::map<Node, Node>& model);

}
}  // namespace theory
}  // namespace cvc5

#endif
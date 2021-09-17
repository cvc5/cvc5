
#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_EVALUATOR_H
#define CVC5__THEORY__ARITH__ARITH_EVALUATOR_H

#include "expr/node.h"
#include "smt/env.h"

namespace cvc5 {
namespace theory {
namespace arith {

bool isExpressionZero(Env& env, Node expr, const std::map<Node, Node>& model);

}
}
}

#endif
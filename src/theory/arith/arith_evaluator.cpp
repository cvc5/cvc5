/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic evaluator.
 */
#include "theory/arith/arith_evaluator.h"

#include "theory/arith/nl/poly_conversion.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "util/real_algebraic_number.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

std::optional<bool> isExpressionZero(Env& env, Node expr, const ArithSubs& subs)
{
  // Substitute constants and rewrite
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
  // we use an arithmetic substitution, which does not traverse into
  // terms that do not belong to the core theory of arithmetic.
  expr = subs.applyArith(expr);
  expr = env.getRewriter()->rewrite(expr);
  if (expr.isConst())
  {
    return expr.getConst<Rational>().isZero();
  }
  if (expr.getKind() == Kind::REAL_ALGEBRAIC_NUMBER)
  {
    return expr.getOperator().getConst<RealAlgebraicNumber>().isZero();
  }
  return std::nullopt;
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

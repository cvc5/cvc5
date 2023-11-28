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
 * Node utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__NODE_UTILS_H
#define CVC5__THEORY__ARITH__REWRITER__NODE_UTILS_H

#include "base/check.h"
#include "expr/node.h"
#include "util/integer.h"
#include "util/rational.h"
#include "util/real_algebraic_number.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace rewriter {

/**
 * Check whether the node is an arithmetic atom, that is one of LT, LEQ, EQUAL,
 * GEQ, GT, IS_INTEGER, DIVISIBLE.
 * Note that DISTINCT somehow belongs to this list, but should already be
 * eliminated at this point.
 */
inline bool isAtom(TNode n)
{
  switch (n.getKind())
  {
    case Kind::LT:
    case Kind::LEQ:
    case Kind::EQUAL:
    case Kind::GEQ:
    case Kind::GT:
    case Kind::IS_INTEGER:
    case Kind::DIVISIBLE: return true;
    case Kind::DISTINCT: Unreachable(); return false;
    default: return false;
  }
}

/** Check whether the node wraps a real algebraic number. */
inline bool isRAN(TNode n)
{
  return n.getKind() == Kind::REAL_ALGEBRAIC_NUMBER;
}
/** Retrieve the wrapped a real algebraic number. Asserts isRAN(n) */
inline const RealAlgebraicNumber& getRAN(TNode n)
{
  Assert(isRAN(n));
  return n.getOperator().getConst<RealAlgebraicNumber>();
}

/**
 * Check whether the parent has a child that is a constant zero. If so, return
 * this child. Otherwise, return std::nullopt. Works on any kind of iterable,
 * i.e. both a node or a vector of nodes.
 */
template <typename Iterable>
std::optional<TNode> getZeroChild(const Iterable& parent)
{
  for (const auto& node : parent)
  {
    if (node.isConst() && node.template getConst<Rational>().isZero())
    {
      return node;
    }
  }
  return {};
}

/** Create a Boolean constant node */
inline Node mkConst(bool value)
{
  return NodeManager::currentNM()->mkConst(value);
}
/** Create an integer constant node */
inline Node mkConst(const Integer& value)
{
  return NodeManager::currentNM()->mkConstInt(value);
}

/** Create a real algebraic number node */
inline Node mkConst(const RealAlgebraicNumber& value)
{
  return NodeManager::currentNM()->mkRealAlgebraicNumber(value);
}

/** Make a nonlinear multiplication from the given factors */
inline Node mkNonlinearMult(const std::vector<Node>& factors)
{
  auto* nm = NodeManager::currentNM();
  switch (factors.size())
  {
    case 0: return nm->mkConstInt(Rational(1));
    case 1: return factors[0];
    default: return nm->mkNode(Kind::NONLINEAR_MULT, factors);
  }
}

/**
 * Create the product of `multiplicity * monomial`. Assumes that the monomial is
 * either a product of non-values (neither rational nor real algebraic numbers)
 * or a rational constant.
 * If the monomial is a constant, return the product of the two numbers. If the
 * multiplicity is one, return the monomial. Otherwise return `(MULT
 * multiplicity monomial)`.
 */
Node mkMultTerm(const Rational& multiplicity, TNode monomial);

/**
 * Create the product of `multiplicity * monomial`. Assumes that the monomial is
 * either a product of non-values (neither rational nor real algebraic numbers)
 * or a rational constant.
 * If multiplicity is rational, defer to the appropriate overload. If the
 * monomial is one, return the product of the two numbers. Otherwise return the
 * nonlinear product of the two, i.e. `(NONLINEAR_MULT multiplicity *monomial)`.
 */
Node mkMultTerm(const RealAlgebraicNumber& multiplicity, TNode monomial);

/**
 * Create the product of `multiplicity * monomial`, where the monomial is given
 * as the (implicitly multiplied, possibly unsorted) list of children. Assumes
 * that monomial is either empty (implicitly one) or  a list of non-values
 * (neither rational nor real algebraic numbers). If multiplicity is rational,
 * sort the monomial, create a nonlinear mult term and defer to the appropriate
 * overload. Otherwise return the nonlinear product of the two, i.e.
 * `(NONLINEAR_MULT multiplicity *monomial)`. The monomial is taken as rvalue as
 * it may be modified in the process.
 *
 */
Node mkMultTerm(const RealAlgebraicNumber& multiplicity,
                std::vector<Node>&& monomial);

/**
 * Remove TO_REAL from t, returns t[0] if t has kind TO_REAL.
 */
TNode removeToReal(TNode t);
/**
 * Ensure that t has real type if tn is the real type. Do so by applying
 * TO_REAL to t.
 */
Node maybeEnsureReal(TypeNode tn, TNode t);
/** Same as above, without a check for the type of tn. */
Node ensureReal(TNode t);

}  // namespace rewriter
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif

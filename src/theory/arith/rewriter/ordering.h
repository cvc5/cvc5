/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Comparator utilities for the arithmetic rewriter.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__REWRITER__ORDERING_H
#define CVC5__THEORY__ARITH__REWRITER__ORDERING_H

#include "base/check.h"
#include "expr/node.h"

namespace cvc5::internal::theory::arith::rewriter {

/**
 * Implements an ordering on arithmetic leaf nodes. We expect that values have
 * already been combined, i.e., there shall only be a single rational and a
 * single real algebraic number. It broadly categorizes leaf nodes into
 * rationals, real algebraic numbers, integers, variables, and the rest.
 * The ordering is built as follows:
 * - rationals come first
 * - real algebraic numbers come second
 * - real terms come before integer terms
 * - variables come before non-variable terms
 * - finally, fall back to node ordering
 */
struct LeafNodeComparator
{
  /** Implements operator<(a, b) as described above */
  bool operator()(TNode a, TNode b) const
  {
    if (a == b) return false;

    bool aIsConst = a.isConst();
    bool bIsConst = b.isConst();
    if (aIsConst != bIsConst) return aIsConst;
    Assert(!aIsConst && !bIsConst) << "Rationals should be combined";

    bool aIsRAN = a.getKind() == Kind::REAL_ALGEBRAIC_NUMBER;
    bool bIsRAN = b.getKind() == Kind::REAL_ALGEBRAIC_NUMBER;
    if (aIsRAN != bIsRAN) return aIsRAN;
    Assert(!aIsRAN && !bIsRAN) << "real algebraic numbers should be combined";

    bool aIsInt = a.getType().isInteger();
    bool bIsInt = b.getType().isInteger();
    if (aIsInt != bIsInt) return !aIsInt;

    bool aIsVar = a.isVar();
    bool bIsVar = b.isVar();
    if (aIsVar != bIsVar) return aIsVar;

    return a < b;
  }
};

/**
 * Implements an ordering on arithmetic terms or summands. We expect these terms
 * to be products (MULT or NONLINEAR_MULT), though products of zero or one node
 * are not actually represented as such. For individual factors of the product,
 * we rely on the ordering from LeafNodeComparator. Furthermore, we expect the
 * individual factors to be sorted according to LeafNodeComparator. The ordering
 * is built as follows:
 * - single factors come first (everything that is MULT or NONLINEAR_MULT)
 * - multiplications with less factors come first
 * - multiplications are compared lexicographically
 */
struct TermComparator
{
  /** Implements operator<(a, b) as described above */
  bool operator()(TNode a, TNode b) const
  {
    if (a == b) return false;

    bool aIsMult =
        a.getKind() == Kind::MULT || a.getKind() == Kind::NONLINEAR_MULT;
    bool bIsMult =
        b.getKind() == Kind::MULT || b.getKind() == Kind::NONLINEAR_MULT;
    if (aIsMult != bIsMult) return !aIsMult;

    if (!aIsMult)
    {
      return LeafNodeComparator()(a, b);
    }

    size_t aLen = a.getNumChildren();
    size_t bLen = b.getNumChildren();
    if (aLen != bLen) return aLen < bLen;

    for (size_t i = 0; i < aLen; ++i)
    {
      if (a[i] != b[i])
      {
        return LeafNodeComparator()(a[i], b[i]);
      }
    }
    Unreachable() << "Nodes are different, but have the same content";
    return false;
  }
};

}  // namespace cvc5::internal::theory::arith::rewriter

#endif

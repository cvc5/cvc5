/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Type for rewrites for bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__REWRITES_H
#define CVC5__THEORY__BAGS__REWRITES_H

#include <iosfwd>

namespace cvc5::internal {
namespace theory {
namespace bags {

/** Types of rewrites used by bags
 *
 * This rewrites are documented where they are used in the rewriter.
 */
enum class Rewrite : uint32_t
{
  NONE,  // no rewrite happened
  AGGREGATE_CONST,
  BAG_MAKE_COUNT_NEGATIVE,
  CARD_DISJOINT,
  CARD_BAG_MAKE,
  CHOOSE_BAG_MAKE,
  CONSTANT_EVALUATION,
  COUNT_EMPTY,
  COUNT_BAG_MAKE,
  DUPLICATE_REMOVAL_BAG_MAKE,
  EQ_CONST_FALSE,
  EQ_REFL,
  EQ_SYM,
  FILTER_CONST,
  FILTER_BAG_MAKE,
  FILTER_UNION_DISJOINT,
  FROM_SINGLETON,
  FOLD_BAG,
  FOLD_CONST,
  FOLD_UNION_DISJOINT,
  IDENTICAL_NODES,
  INTERSECTION_EMPTY_LEFT,
  INTERSECTION_EMPTY_RIGHT,
  INTERSECTION_SAME,
  INTERSECTION_SHARED_LEFT,
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_BAG_MAKE,
  MAP_CONST,
  MAP_BAG_MAKE,
  MAP_UNION_DISJOINT,
  MEMBER,
  PARTITION_CONST,
  PRODUCT_EMPTY,
  REMOVE_FROM_UNION,
  REMOVE_MIN,
  REMOVE_RETURN_LEFT,
  REMOVE_SAME,
  SUB_BAG,
  SUBTRACT_DISJOINT_SHARED_LEFT,
  SUBTRACT_DISJOINT_SHARED_RIGHT,
  SUBTRACT_FROM_UNION,
  SUBTRACT_MIN,
  SUBTRACT_RETURN_LEFT,
  SUBTRACT_SAME,
  TO_SINGLETON,
  UNION_DISJOINT_EMPTY_LEFT,
  UNION_DISJOINT_EMPTY_RIGHT,
  UNION_DISJOINT_MAX_MIN,
  UNION_MAX_EMPTY,
  UNION_MAX_SAME_OR_EMPTY,
  UNION_MAX_UNION_LEFT,
  UNION_MAX_UNION_RIGHT
};

/**
 * Converts an rewrite to a string. Note: This function is also used in
 * `safe_print()`. Changing this functions name or signature will result in
 * `safe_print()` printing "<unsupported>" instead of the proper strings for
 * the enum values.
 *
 * @param r The rewrite
 * @return The name of the rewrite
 */
const char* toString(Rewrite r);

/**
 * Writes an rewrite name to a stream.
 *
 * @param out The stream to write to
 * @param r The rewrite to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, Rewrite r);

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__REWRITES_H */

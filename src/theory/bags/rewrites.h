/*********************                                                        */
/*! \file rewrites.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Type for rewrites for bags.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BAGS__REWRITES_H
#define CVC4__THEORY__BAGS__REWRITES_H

#include <iosfwd>

namespace CVC4 {
namespace theory {
namespace bags {

/** Types of rewrites used by bags
 *
 * This rewrites are documented where they are used in the rewriter.
 */
enum class Rewrite : uint32_t
{
  NONE, // no rewrite happened
  CARD_DISJOINT,
  CARD_MK_BAG,
  CHOOSE_MK_BAG,
  CONSTANT_EVALUATION,
  COUNT_EMPTY,
  COUNT_MK_BAG,
  IDENTICAL_NODES,
  INTERSECTION_EMPTY_LEFT,
  INTERSECTION_EMPTY_RIGHT,
  INTERSECTION_SAME,
  INTERSECTION_SHARED_LEFT,
  INTERSECTION_SHARED_RIGHT,
  IS_SINGLETON_MK_BAG,
  MK_BAG_COUNT_NEGATIVE,
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
}  // namespace CVC4

#endif /* CVC4__THEORY__BAGS__REWRITES_H */

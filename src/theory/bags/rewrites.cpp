/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of inference information utility.
 */

#include "theory/bags/rewrites.h"

#include <iostream>

namespace cvc5::internal {
namespace theory {
namespace bags {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::NONE: return "NONE";
    case Rewrite::AGGREGATE_CONST: return "AGGREGATE_CONST";
    case Rewrite::BAG_MAKE_COUNT_NEGATIVE: return "BAG_MAKE_COUNT_NEGATIVE";
    case Rewrite::CARD_DISJOINT: return "CARD_DISJOINT";
    case Rewrite::CARD_BAG_MAKE: return "CARD_BAG_MAKE";
    case Rewrite::CHOOSE_BAG_MAKE: return "CHOOSE_BAG_MAKE";
    case Rewrite::CONSTANT_EVALUATION: return "CONSTANT_EVALUATION";
    case Rewrite::COUNT_EMPTY: return "COUNT_EMPTY";
    case Rewrite::COUNT_BAG_MAKE: return "COUNT_BAG_MAKE";
    case Rewrite::DUPLICATE_REMOVAL_BAG_MAKE:
      return "DUPLICATE_REMOVAL_BAG_MAKE";
    case Rewrite::EQ_CONST_FALSE: return "EQ_CONST_FALSE";
    case Rewrite::EQ_REFL: return "EQ_REFL";
    case Rewrite::EQ_SYM: return "EQ_SYM";
    case Rewrite::FILTER_CONST: return "FILTER_CONST";
    case Rewrite::FILTER_BAG_MAKE: return "FILTER_BAG_MAKE";
    case Rewrite::FILTER_UNION_DISJOINT: return "FILTER_UNION_DISJOINT";
    case Rewrite::FROM_SINGLETON: return "FROM_SINGLETON";
    case Rewrite::FOLD_BAG: return "FOLD_BAG";
    case Rewrite::FOLD_CONST: return "FOLD_CONST";
    case Rewrite::FOLD_UNION_DISJOINT: return "FOLD_UNION_DISJOINT";
    case Rewrite::IDENTICAL_NODES: return "IDENTICAL_NODES";
    case Rewrite::INTERSECTION_EMPTY_LEFT: return "INTERSECTION_EMPTY_LEFT";
    case Rewrite::INTERSECTION_EMPTY_RIGHT: return "INTERSECTION_EMPTY_RIGHT";
    case Rewrite::INTERSECTION_SAME: return "INTERSECTION_SAME";
    case Rewrite::INTERSECTION_SHARED_LEFT: return "INTERSECTION_SHARED_LEFT";
    case Rewrite::INTERSECTION_SHARED_RIGHT: return "INTERSECTION_SHARED_RIGHT";
    case Rewrite::IS_SINGLETON_BAG_MAKE: return "IS_SINGLETON_BAG_MAKE";
    case Rewrite::MAP_CONST: return "MAP_CONST";
    case Rewrite::MAP_BAG_MAKE: return "MAP_BAG_MAKE";
    case Rewrite::MAP_UNION_DISJOINT: return "MAP_UNION_DISJOINT";
    case Rewrite::MEMBER: return "MEMBER";
    case Rewrite::PARTITION_CONST: return "PARTITION_CONST";
    case Rewrite::PRODUCT_EMPTY: return "PRODUCT_EMPTY";
    case Rewrite::REMOVE_FROM_UNION: return "REMOVE_FROM_UNION";
    case Rewrite::REMOVE_MIN: return "REMOVE_MIN";
    case Rewrite::REMOVE_RETURN_LEFT: return "REMOVE_RETURN_LEFT";
    case Rewrite::REMOVE_SAME: return "REMOVE_SAME";
    case Rewrite::SUB_BAG: return "SUB_BAG";
    case Rewrite::SUBTRACT_DISJOINT_SHARED_LEFT:
      return "SUBTRACT_DISJOINT_SHARED_LEFT";
    case Rewrite::SUBTRACT_DISJOINT_SHARED_RIGHT:
      return "SUBTRACT_DISJOINT_SHARED_RIGHT";
    case Rewrite::SUBTRACT_FROM_UNION: return "SUBTRACT_FROM_UNION";
    case Rewrite::SUBTRACT_MIN: return "SUBTRACT_MIN";
    case Rewrite::SUBTRACT_RETURN_LEFT: return "SUBTRACT_RETURN_LEFT";
    case Rewrite::SUBTRACT_SAME: return "SUBTRACT_SAME";
    case Rewrite::UNION_DISJOINT_EMPTY_LEFT: return "UNION_DISJOINT_EMPTY_LEFT";
    case Rewrite::TO_SINGLETON: return "TO_SINGLETON";
    case Rewrite::UNION_DISJOINT_EMPTY_RIGHT:
      return "UNION_DISJOINT_EMPTY_RIGHT";
    case Rewrite::UNION_DISJOINT_MAX_MIN: return "UNION_DISJOINT_MAX_MIN";
    case Rewrite::UNION_MAX_EMPTY: return "UNION_MAX_EMPTY";
    case Rewrite::UNION_MAX_SAME_OR_EMPTY: return "UNION_MAX_SAME_OR_EMPTY";
    case Rewrite::UNION_MAX_UNION_LEFT: return "UNION_MAX_UNION_LEFT";
    case Rewrite::UNION_MAX_UNION_RIGHT: return "UNION_MAX_UNION_RIGHT";

    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

/*********************                                                        */
/*! \file rewrites.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/bags/rewrites.h"

#include <iostream>

namespace CVC4 {
namespace theory {
namespace bags {

const char* toString(Rewrite r)
{
  switch (r)
  {
    case Rewrite::NONE: return "NONE";
    case Rewrite::CARD_DISJOINT: return "CARD_DISJOINT";
    case Rewrite::CARD_MK_BAG: return "CARD_MK_BAG";
    case Rewrite::CHOOSE_MK_BAG: return "CHOOSE_MK_BAG";
    case Rewrite::CONSTANT_EVALUATION: return "CONSTANT_EVALUATION";
    case Rewrite::COUNT_EMPTY: return "COUNT_EMPTY";
    case Rewrite::COUNT_MK_BAG: return "COUNT_MK_BAG";
    case Rewrite::IDENTICAL_NODES: return "IDENTICAL_NODES";
    case Rewrite::INTERSECTION_EMPTY_LEFT: return "INTERSECTION_EMPTY_LEFT";
    case Rewrite::INTERSECTION_EMPTY_RIGHT: return "INTERSECTION_EMPTY_RIGHT";
    case Rewrite::INTERSECTION_SAME: return "INTERSECTION_SAME";
    case Rewrite::INTERSECTION_SHARED_LEFT: return "INTERSECTION_SHARED_LEFT";
    case Rewrite::INTERSECTION_SHARED_RIGHT: return "INTERSECTION_SHARED_RIGHT";
    case Rewrite::IS_SINGLETON_MK_BAG: return "IS_SINGLETON_MK_BAG";
    case Rewrite::MK_BAG_COUNT_NEGATIVE: return "MK_BAG_COUNT_NEGATIVE";
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
}  // namespace CVC4

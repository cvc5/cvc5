/*********************                                                        */
/*! \file care_graph.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The care graph datastructure.
 **
 ** The care graph datastructure.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__CARE_GRAPH_H
#define __CVC4__THEORY__CARE_GRAPH_H

#include <set>

#include "expr/kind.h"  // For TheoryId.
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * A (ordered) pair of terms a theory cares about.
 */
struct CarePair {
  const TNode a, b;
  const TheoryId theory;

  CarePair(TNode a, TNode b, TheoryId theory)
      : a(a < b ? a : b), b(a < b ? b : a), theory(theory) {}

  bool operator==(const CarePair& other) const {
    return (theory == other.theory) && (a == other.a) && (b == other.b);
  }

  bool operator<(const CarePair& other) const {
    if (theory < other.theory) return true;
    if (theory > other.theory) return false;
    if (a < other.a) return true;
    if (a > other.a) return false;
    return b < other.b;
  }

}; /* struct CarePair */

/**
 * A set of care pairs.
 */
typedef std::set<CarePair> CareGraph;

}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__CARE_GRAPH_H */

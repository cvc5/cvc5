/*********************                                                        */
/*! \file care_graph.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The care graph datastructure.
 **
 ** The care graph datastructure.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__CARE_GRAPH_H
#define CVC4__THEORY__CARE_GRAPH_H

#include <set>

#include "expr/kind.h"  // For TheoryId.
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/**
 * A (ordered) pair of terms a theory cares about.
 */
struct CarePair {
  const TNode d_a, d_b;
  const TheoryId d_theory;

  CarePair(TNode a, TNode b, TheoryId theory)
      : d_a(a < b ? a : b), d_b(a < b ? b : a), d_theory(theory)
  {
  }

  bool operator==(const CarePair& other) const {
    return (d_theory == other.d_theory) && (d_a == other.d_a)
           && (d_b == other.d_b);
  }

  bool operator<(const CarePair& other) const {
    if (d_theory < other.d_theory) return true;
    if (d_theory > other.d_theory) return false;
    if (d_a < other.d_a) return true;
    if (d_a > other.d_a) return false;
    return d_b < other.d_b;
  }

}; /* struct CarePair */

/**
 * A set of care pairs.
 */
typedef std::set<CarePair> CareGraph;

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__CARE_GRAPH_H */

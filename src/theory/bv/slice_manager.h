/*
 * slice_manager.h
 *
 *  Created on: Feb 16, 2011
 *      Author: dejan
 */

#pragma once

#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/equality_engine.h"

#include <vector>

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * Slice manager should keep the database of slices for the core theory leaf terms, for example
 *
 * term                           core leaf terms
 * ----------------------------------------------
 * (x + y)[31:0]                  x + y
 * a[10:0]@a[11:10]@(b + c)[1:0]  a, b, (b + c)
 * (a << 5)[10]                   (a << 5)
 *
 * If an (dis-)equality is added to the system, we refine the slicing in order to align the extracts, for example
 *
 * equality                       slicing
 * ----------------------------------------------
 * x = y                          x[32,0], y[32,0]
 * x@y = z                        x[32,0], y[32,0], z[64,32,0]
 * x@y = z, x[31:16] = y[15:0]    x[32,16,0], y[32,16,0], z[64,48,32,16,0]
 *
 * As a result of the slicing the slicing equalities are added to the equality engine, using the (associative)
 * concat function that is generated for the equality manager, for example
 *
 * equality                       added equalities
 * ----------------------------------------------
 * x = y                          none
 * x@y = z                        z = concat(z[63:32],z[31:0])
 * x@y = z, x[31:16] = y[15:0]    z = concat(z[63:32],z[31:0]),
 *                                z[63:32] = concat(z[63:48], z[47:32]),
 *                                z[31:0] = concat(z[31:16], z[15:0])
 *
 * In the last example, since concat is associative, the equality engine will know that z = concat(z[63:48], z[47:32],
 * z[31:16], z[15:0]).
 *
 */
template <class TheoryBitvector>
class SliceManager {

  /** The equality engine theory of bit-vectors is using */
  typedef typename TheoryBitvector::BvEqualityEngine EqualityEngine;

  /** The theory of bitvectors */
  TheoryBitvector& d_theoryBitvector;

  /** The equality engine */
  EqualityEngine& d_equalityEngine;

  /** The id of the concatenation function */
  size_t d_concatFunctionId;

public:

  SliceManager(TheoryBitvector& theoryBitvector)
  : d_theoryBitvector(theoryBitvector), d_equalityEngine(theoryBitvector.getEqualityEngine()) {
    // We register the concatentation with the equality engine
    d_concatFunctionId = d_equalityEngine.newFunction();
  }

  inline size_t getConcatFunctionId() const { return d_concatFunctionId; }

  /**
   * Adds the equality (lhs = rhs) to the slice manager. This will not add the equalities to the equality manager,
   * but will slice the equality according to the current slicing in order to align all the slices. The terms that
   * get slices get sent to the theory engine as equalities, i.e if we slice x[10:0] into x[10:5]@x[4:0] equality
   * engine gets the assertion x[10:0] = concat(x[10:5], x[4:0]).
   */
  inline void addEquality(TNode lhs, TNode rhs, std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices);
};


template <class TheoryBitvector>
void SliceManager<TheoryBitvector>::addEquality(TNode lhs, TNode rhs, std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices) {
  Debug("theory::bv::slicing") << "addEquality(" << lhs << "," << rhs << ")";
  lhsSlices.push_back(lhs);
  rhsSlices.push_back(rhs);
}

} // Namespace bv
} // Namespace theory
} // Namespace CVC4

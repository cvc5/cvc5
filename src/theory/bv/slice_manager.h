/*
 * slice_manager.h
 *
 *  Created on: Feb 16, 2011
 *      Author: dejan
 */

#pragma once

#include "context/cdo.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/equality_engine.h"
#include "theory/bv/cd_set_collection.h"

#include <map>
#include <vector>

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * Representation of the slice points in tree.
 */
class slice_point
{
public:

  /** Number of bits we use for the index of the slice */
  static const size_t s_slice_index_bits = 31;
  /** Number of bits we use for the index of the slice_point in the slice memory (reference) */
  static const size_t s_slice_point_reference_bits = 32;
  /** The null reference (maximal number in the given bits) */
  static const size_t null = (1llu << s_slice_point_reference_bits) - 1;

  /** Type of the reference for the outside world */
  typedef size_t reference_type;

  /** Type of the value for the outside world */
  typedef size_t value_type;

private:

  /** The value of the slice point (bit index) */
  size_t d_value       : s_slice_index_bits;
  /** Is this the left child */
  size_t d_isLeftChild : 1;
  /** Reference to the left in the tree */
  size_t d_left        : s_slice_point_reference_bits;
  /** Reference to the right of the tree */
  size_t d_right       : s_slice_point_reference_bits;
  /** Reference to the parent */
  size_t d_parent      : s_slice_point_reference_bits;

public:

  slice_point(size_t value, size_t left, size_t right, size_t parent, bool isLeftChild)
  : d_value(value), d_isLeftChild(isLeftChild ? 1 : 0), d_left(left), d_right(right), d_parent(parent) {}

  bool isLeft() const  { return d_isLeftChild == 1; }
  bool isRight() const { return d_isLeftChild == 0; }

  bool hasLeft() const   { return d_left   != null; }
  bool hasRight() const  { return d_right  != null; }
  bool hasParent() const { return d_parent != null; }

  reference_type getLeft() const   { return d_left;   }
  reference_type getRight() const  { return d_right;  }
  reference_type getParent() const { return d_parent; }

  void removeLeft()  { Assert(d_left  != null); d_left = null;  }
  void removeRight() { Assert(d_right != null); d_right = null; }

  void setLeft(reference_type left)   { Assert(d_left  == null && left  != null); d_left  = left;  }
  void setRight(reference_type right) { Assert(d_right == null && right != null); d_right = right; }

  value_type getValue() const { return d_value; }
};

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

public:

  /** The references to backtrackable sets */
  typedef slice_point::reference_type set_reference;

  /** The set collection we'll be using */
  typedef context::BacktrackableSetCollection<std::vector<slice_point>, slice_point, set_reference> set_collection;

  /** The map type from nodes to their references */
  typedef std::map<Node, set_reference> slicing_map;

  /** The equality engine theory of bit-vectors is using */
  typedef typename TheoryBitvector::BvEqualityEngine EqualityEngine;

private:

  /** The theory of bitvectors */
  TheoryBitvector& d_theoryBitvector;

  /** The equality engine */
  EqualityEngine& d_equalityEngine;

  /** The id of the concatenation function */
  size_t d_concatFunctionId;

  /** The collection of backtrackable sets */
  set_collection d_setCollection;

  /**
   * A map from base nodes to slice points. For each node, the slice points are
   * 0 = i_1 < i_2 < ... < i_n = size, and the slices are
   *            x[i_n-1:i_{n-1}]@x[i_{n-1}-1:i_{n-2}]@...@x[i_2-1:i_1]
   * Each time we add a slict t = t1@t2@...@tn of a term (or a slice), we also notify the equality engine with an
   * extra assertion. Since the equality engine is backtrackable, we will need to backtrack the slices accordingly.
   */
  slicing_map d_nodeSlicing;

public:

  SliceManager(TheoryBitvector& theoryBitvector, context::Context* context)
  : d_theoryBitvector(theoryBitvector), d_equalityEngine(theoryBitvector.getEqualityEngine()), d_setCollection(context) {
    // We register the concatentation with the equality engine
    d_concatFunctionId = d_equalityEngine.newFunction("bv_concat", true);
  }

  inline size_t getConcatFunctionId() const { return d_concatFunctionId; }

  /**
   * Adds the equality (lhs = rhs) to the slice manager. This will not add the equalities to the equality manager,
   * but will slice the equality according to the current slicing in order to align all the slices. The terms that
   * get slices get sent to the theory engine as equalities, i.e if we slice x[10:0] into x[10:5]@x[4:0] equality
   * engine gets the assertion x[10:0] = concat(x[10:5], x[4:0]).
   */
  inline void addEquality(TNode lhs, TNode rhs, std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices);

private:

  /**
   * Slices up lhs and rhs and returns the slices in lhsSlices and rhsSlices
   */
  inline void slice(std::vector<Node>& lhs, std::vector<Node>& rhs,
                    std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices);

  /**
   * Returns true if the term is already sliced wrt the current slicing. Note that, for example, even though
   * the slicing is empty, x[i:j] is considered sliced. Sliced means that there is no slice points between i and j.
   */
  inline bool isSliced(TNode node) const;

  /**
   * Slices the term wrt the current slicing. When done, isSliced returns true
   */
  inline void slice(TNode node, std::vector<Node>& sliced);

  /**
   * Returns the base term in the core theory of the given term, i.e.
   * x            => x
   * x[i:j]       => x
   * (x + y)      => x+y
   * (x + y)[i:j] => x+y
   */
  static inline TNode baseTerm(TNode node);

  /**
   * Adds a new slice to the slice set of the given base term.
   */
  inline void addSlice(Node baseTerm, unsigned slicePoint);
};


template <class TheoryBitvector>
void SliceManager<TheoryBitvector>::addSlice(Node baseTerm, unsigned slicePoint) {
}

template <class TheoryBitvector>
void SliceManager<TheoryBitvector>::addEquality(TNode lhs, TNode rhs, std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices) {

  Debug("slicing") << "SliceMagager::addEquality(" << lhs << "," << rhs << ")" << std::endl;

  // The concatenations on the left-hand side (reverse order, first is on top)
  std::vector<Node> lhsTerms;
  if (lhs.getKind() == kind::BITVECTOR_CONCAT) {
    for (int i = (int) lhs.getNumChildren() - 1; i >= 0; -- i) {
      lhsTerms.push_back(lhs[i]);
    }
  } else {
    lhsTerms.push_back(lhs);
  }

  // The concatenations on the right-hand side (reverse order, first is on top)
  std::vector<Node> rhsTerms;
  if (rhs.getKind() == kind::BITVECTOR_CONCAT) {
    for (int i = (int) rhs.getNumChildren() - 1; i >= 0; --i) {
      rhsTerms.push_back(rhs[i]);
    }
  } else {
    rhsTerms.push_back(rhs);
  }

  // Slice the individual terms to align them
  slice(lhsTerms, rhsTerms, lhsSlices, rhsSlices);
}

template <class TheoryBitvector>
void SliceManager<TheoryBitvector>::slice(std::vector<Node>& lhs, std::vector<Node>& rhs,
                                          std::vector<Node>& lhsSlices, std::vector<Node>& rhsSlices) {

  Debug("slicing") << "SliceManager::slice()" << std::endl;

  // Go through the work-list and align
  while (!lhs.empty()) {

    Assert(!rhs.empty());

    // The terms that we need to slice
    Node lhsTerm = lhs.back();
    Node rhsTerm = rhs.back();
    Debug("slicing") << "slicing: " << lhsTerm << " and " << rhsTerm << std::endl;

    // If the terms are not sliced wrt the current slicing, we have them sliced
    lhs.pop_back();
    if (!isSliced(lhsTerm)) {
      slice(lhsTerm, lhs);
      continue;
    }
    rhs.pop_back();
    if (!isSliced(rhsTerm)) {
      slice(rhsTerm, rhs);
    }

    // If the slices are of the same size we do the additional work
    unsigned lhsSize = utils::getSize(lhsTerm);
    unsigned rhsSize = utils::getSize(rhsTerm);
    if (lhsSize == rhsSize) {
      // If they are over the same base terms, we need to do something
      TNode lhsBaseTerm = baseTerm(lhsTerm);
      TNode rhsBaseTerm = baseTerm(rhsTerm);
      if (lhsBaseTerm == rhsBaseTerm) {
        // x[i_1:j_1] vs x[i_2:j_2]
      } else {
        // x[i_1:j_1] vs y[i_2:j_2]
      }
      lhsSlices.push_back(lhsTerm);
      rhsSlices.push_back(rhsTerm);
      continue;
    } else {
      // They are not of equal sizes, so we slice one
      if (lhsSize < rhsSize) {
        // We need to cut a piece of rhs
      } else {
        // We need to cut a piece of lhs
      }
    }
  }
}

template <class TheoryBitvector>
bool SliceManager<TheoryBitvector>::isSliced(TNode node) const {

  Debug("slicing") << "SliceManager::isSliced(" << node << ")" << std::endl;

  bool result = false;

  // Constants are always sliced
  if (node.getKind() == kind::CONST_BITVECTOR) {
    result = true;
  } else {
    // The indices of the beginning and end
    Kind nodeKind = node.getKind();
    unsigned high = nodeKind == kind::BITVECTOR_EXTRACT ? utils::getExtractHigh(node) : utils::getSize(node) - 1;
    unsigned low  = nodeKind == kind::BITVECTOR_EXTRACT ? utils::getExtractLow(node) : 0;

    // Get the base term
    TNode nodeBase = baseTerm(node);
    Assert(nodeBase.getKind() != kind::BITVECTOR_CONCAT);
    Assert(nodeBase.getKind() != kind::CONST_BITVECTOR);

    // Get the base term slice set
    slicing_map::const_iterator find = d_nodeSlicing.find(nodeBase);
    // If no slices, it's just a term, so we are done, UNLESS it's an extract
    if (find == d_nodeSlicing.end()) {
      result = nodeKind != kind::BITVECTOR_EXTRACT;
    } else {
      // Check whether there is a slice point in [high, low), if there is the term is not sliced.
      // Hence, if we look for the upper bound of low, and it is higher than high, it is sliced.
      result = d_setCollection.count(find->second, low + 1, high) > 0;
    }
  }

  Debug("slicing") << "SliceManager::isSliced(" << node << ") => " << (result ? "true" : "false") << std::endl;
  return result;
}

template <class TheoryBitvector>
inline void SliceManager<TheoryBitvector>::slice(TNode node, std::vector<Node>& sliced) {

  Debug("slicing") << "SliceManager::slice(" << node << ")" << endl;

  Assert(!isSliced(node));

  // The indices of the beginning and (one past) end
  unsigned high = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractHigh(node) + 1 : utils::getSize(node);
  unsigned low  = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractLow(node) : 0;

  // Get the base term
  TNode nodeBase = baseTerm(node);
  Assert(nodeBase.getKind() != kind::BITVECTOR_CONCAT);
  Assert(nodeBase.getKind() != kind::CONST_BITVECTOR);

  // Get the base term slice set
  set_collection::reference_type nodeSliceSet = d_nodeSlicing[nodeBase];
  Debug("slicing") << "SliceManager::slice(" << node << "): current: " << d_setCollection.toString(nodeSliceSet) << endl;
  std::vector<size_t> slicePoints;
  d_setCollection.getElements(nodeSliceSet, low + 1, high - 1, slicePoints);

  // Go through all the points i_0 <= low < i_1 < ... < i_{n-1} < high <= i_n from the slice set
  // and generate the slices [i_0:low-1][low:i_1-1] [i_1:i2] ... [i_{n-1}:high-1][high:i_n-1]. They are in reverse order,
  // as they should be
  size_t i_0 = low == 0 ? 0 : d_setCollection.prev(nodeSliceSet, low + 1);
  size_t i_n = high == utils::getSize(nodeBase) ? high: d_setCollection.next(nodeSliceSet, high);

  // Add the new points to the slice set (they might be there already)
  if (high < i_n) {
    std::vector<Node> lastTwoSlices;
    lastTwoSlices.push_back(utils::mkExtract(nodeBase, i_n-1, high));
    lastTwoSlices.push_back(utils::mkExtract(nodeBase, high-1, slicePoints.back()));
    d_equalityEngine.addEquality(utils::mkExtract(nodeBase, i_n-1, slicePoints.back()), utils::mkConcat(lastTwoSlices));
  }

  while (!slicePoints.empty()) {
    sliced.push_back(utils::mkExtract(nodeBase, high-1, slicePoints.back()));
    high = slicePoints.back();
    slicePoints.pop_back();
  }

  if (i_0 < low) {
    std::vector<Node> firstTwoSlices;
    firstTwoSlices.push_back(utils::mkExtract(nodeBase, high-1, low));
    firstTwoSlices.push_back(utils::mkExtract(nodeBase, low-1, i_0));
    d_equalityEngine.addEquality(utils::mkExtract(nodeBase, high-1, i_0), utils::mkConcat(firstTwoSlices));
  }
}

template <class TheoryBitvector>
TNode SliceManager<TheoryBitvector>::baseTerm(TNode node) {
  if (node.getKind() == kind::BITVECTOR_EXTRACT) {
    Assert(node[0].getKind() != kind::BITVECTOR_EXTRACT);
    Assert(node[0].getKind() != kind::CONST_BITVECTOR);
    return node[0];
  } else {
    Assert(node.getKind() != kind::BITVECTOR_CONCAT);
    return node;
  }
}

} // Namespace bv
} // Namespace theory
} // Namespace CVC4

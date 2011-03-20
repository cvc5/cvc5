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
#include <set>
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
  }

  /**
   * Adds the equality (lhs = rhs) to the slice manager. The equality is first normalized according to the equality
   * manager, i.e. each base term is taken from the equality manager, replaced in, and then the whole concatenation
   * normalized and sliced wrt the current slicing. The method will not add the equalities to the equality manager,
   * but instead will slice the equality according to the current slicing in order to align all the slices.
   *
   * The terms that get sliced get sent to the theory engine as equalities, i.e if we slice x[10:0] into x[10:5]@x[4:0]
   * equality engine gets the assertion x[10:0] = concat(x[10:5], x[4:0]).
   *
   * input                                 output                            slicing
   * --------------------------------------------------------------------------------------------------------------
   * x@y = y@x                             x = y, y = x                      empty
   * x[31:0]@x[64:32] = x                  x = x[31:0]@x[63:32]              x:{64,32,0}
   * x@y = 0000@x@0000                     x = 0000@x[7:4], y = x[3:0]@0000  x:{8,4,0}
   *
   */
  inline bool solveEquality(TNode lhs, TNode rhs);

private:

  inline bool solveEquality(TNode lhs, TNode rhs, const std::set<TNode>& assumptions);

  /**
   * Slices up lhs and rhs and returns the slices in lhsSlices and rhsSlices. The slices are not atomic,
   * they are sliced in order to make one of lhs or rhs atomic, the other one can be a concatenation.
   */
  inline bool sliceAndSolve(std::vector<Node>& lhs, std::vector<Node>& rhs, const std::set<TNode>& assumptions);

  /**
   * Returns true if the term is already sliced wrt the current slicing. Note that, for example, even though
   * the slicing is empty, x[i:j] is considered sliced. Sliced means that there is no slice points between i and j.
   */
  inline bool isSliced(TNode node) const;

  /**
   * Slices the term wrt the current slicing. When done, isSliced returns true
   */
  inline bool slice(TNode node, std::vector<Node>& sliced);

  /**
   * Returns the base term in the core theory of the given term, i.e.
   * x            => x
   * x[i:j]       => x
   * (x + y)      => x+y
   * (x + y)[i:j] => x+y
   */
  static inline TNode baseTerm(TNode node);

  /**
   * Adds a new slice to the slice set of the given term.
   */
  inline bool addSlice(Node term, unsigned slicePoint);
};


template <class TheoryBitvector>
bool SliceManager<TheoryBitvector>::addSlice(Node node, unsigned slicePoint) {
  Debug("slicing") << "SliceMagager::addSlice(" << node << "," << slicePoint << ")" << std::endl;

  bool ok = true;

  int low  = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractLow(node) : 0;
  int high = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractHigh(node) + 1: utils::getSize(node);
  slicePoint += low;

  TNode nodeBase = baseTerm(node);

  set_reference sliceSet;
  slicing_map::iterator find = d_nodeSlicing.find(nodeBase);
  if (find == d_nodeSlicing.end()) {
    sliceSet = d_nodeSlicing[nodeBase] = d_setCollection.newSet(slicePoint);
    d_setCollection.insert(sliceSet, low);
    d_setCollection.insert(sliceSet, high);
  } else {
    sliceSet = find->second;
  }

  // What are the points surrounding the new slice point
  int prev = d_setCollection.prev(sliceSet, slicePoint);
  int next = d_setCollection.next(sliceSet, slicePoint);

  // Add the slice to the set
  d_setCollection.insert(sliceSet, slicePoint);
  Debug("slicing") << "SliceMagager::addSlice(" << node << "," << slicePoint << "): current set " << d_setCollection.toString(sliceSet) << std::endl;

  // Add the terms and the equality to the equality engine
  Node t1 = utils::mkExtract(nodeBase, next - 1, slicePoint);
  Node t2 = utils::mkExtract(nodeBase, slicePoint - 1, prev);
  Node nodeSlice = (next == high && prev == low) ? node : utils::mkExtract(nodeBase, next - 1, prev);
  Node concat = utils::mkConcat(t1, t2);

  d_equalityEngine.addTerm(t1);
  d_equalityEngine.addTerm(t2);
  d_equalityEngine.addTerm(nodeSlice);
  d_equalityEngine.addTerm(concat);

  // We are free to add this slice, unless the slice has a representative that's already a concat
  TNode nodeSliceRepresentative = d_equalityEngine.getRepresentative(nodeSlice);
  if (nodeSliceRepresentative.getKind() != kind::BITVECTOR_CONCAT) {
    // Add the slice to the equality engine
    ok = d_equalityEngine.addEquality(nodeSlice, concat, utils::mkTrue());
  } else {
    // If the representative is a concat, we must solve it
    // There is no need do add nodeSlice = concat as we will solve the representative of nodeSlice
    std::set<TNode> assumptions;
    std::vector<TNode> equalities;
    d_equalityEngine.getExplanation(nodeSlice, nodeSliceRepresentative, equalities);
    assumptions.insert(equalities.begin(), equalities.end());
    ok = solveEquality(nodeSliceRepresentative, concat, assumptions);
  }

  Debug("slicing") << "SliceMagager::addSlice(" << node << "," << slicePoint << ") => " << d_setCollection.toString(d_nodeSlicing[nodeBase]) << std::endl;

  return ok;
}

template <class TheoryBitvector>
bool SliceManager<TheoryBitvector>::solveEquality(TNode lhs, TNode rhs) {
  std::set<TNode> assumptions;
  assumptions.insert(lhs.eqNode(rhs));
  bool ok = solveEquality(lhs, rhs, assumptions);
  return ok;
}

template <class TheoryBitvector>
bool SliceManager<TheoryBitvector>::solveEquality(TNode lhs, TNode rhs, const std::set<TNode>& assumptions) {

  Debug("slicing") << "SliceMagager::solveEquality(" << lhs << "," << rhs << "," << utils::setToString(assumptions) << ")" << push << std::endl;

  bool ok;

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
  ok = sliceAndSolve(lhsTerms, rhsTerms, assumptions);

  Debug("slicing") << "SliceMagager::solveEquality(" << lhs << "," << rhs << "," << utils::setToString(assumptions) << ")" << pop << std::endl;

  return ok;
}


template <class TheoryBitvector>
bool SliceManager<TheoryBitvector>::sliceAndSolve(std::vector<Node>& lhs, std::vector<Node>& rhs, const std::set<TNode>& assumptions)
{

  Debug("slicing") << "SliceManager::sliceAndSolve()" << std::endl;

  // Go through the work-list, solve and align
  while (!lhs.empty()) {

    Assert(!rhs.empty());

    Debug("slicing") << "SliceManager::sliceAndSolve(): lhs " << utils::vectorToString(lhs) << std::endl;
    Debug("slicing") << "SliceManager::sliceAndSolve(): rhs " << utils::vectorToString(rhs) << std::endl;

    // The terms that we need to slice
    Node lhsTerm = lhs.back();
    Node rhsTerm = rhs.back();

    Debug("slicing") << "SliceManager::sliceAndSolve(): " << lhsTerm << " : " << rhsTerm << std::endl;

    // If the terms are not sliced wrt the current slicing, we have them sliced
    lhs.pop_back();
    if (!isSliced(lhsTerm)) {
      if (!slice(lhsTerm, lhs)) return false;
      Debug("slicing") << "SliceManager::sliceAndSolve(): lhs sliced" << std::endl;
      continue;
    }
    rhs.pop_back();
    if (!isSliced(rhsTerm)) {
      if (!slice(rhsTerm, rhs)) return false;
      // We also need to put lhs back
      lhs.push_back(lhsTerm);
      Debug("slicing") << "SliceManager::sliceAndSolve(): rhs sliced" << std::endl;
      continue;
    }

    Debug("slicing") << "SliceManager::sliceAndSolve(): both lhs and rhs sliced already" << std::endl;

    // The solving concatenation
    std::vector<Node> concatTerms;

    // If the slices are of the same size we do the additional work
    int sizeDifference = utils::getSize(lhsTerm) - utils::getSize(rhsTerm);

    // We slice constants immediately
    if (sizeDifference > 0 && lhsTerm.getKind() == kind::CONST_BITVECTOR) {
      BitVector low  = lhsTerm.getConst<BitVector>().extract(utils::getSize(rhsTerm) - 1, 0);
      BitVector high = lhsTerm.getConst<BitVector>().extract(utils::getSize(lhsTerm) - 1, utils::getSize(rhsTerm));
      lhs.push_back(utils::mkConst(low));
      lhs.push_back(utils::mkConst(high));
      rhs.push_back(rhsTerm);
      continue;
    }
    if (sizeDifference < 0 && rhsTerm.getKind() == kind::CONST_BITVECTOR) {
      BitVector low  = rhsTerm.getConst<BitVector>().extract(utils::getSize(lhsTerm) - 1, 0);
      BitVector high = rhsTerm.getConst<BitVector>().extract(utils::getSize(rhsTerm) - 1, utils::getSize(lhsTerm));
      rhs.push_back(utils::mkConst(low));
      rhs.push_back(utils::mkConst(high));
      lhs.push_back(lhsTerm);
      continue;
    }

    enum SolvingFor {
      SOLVING_FOR_LHS,
      SOLVING_FOR_RHS
    } solvingFor = sizeDifference < 0 || lhsTerm.getKind() == kind::CONST_BITVECTOR ? SOLVING_FOR_RHS : SOLVING_FOR_LHS;

    Debug("slicing") << "SliceManager::sliceAndSolve(): " << (solvingFor == SOLVING_FOR_LHS ? "solving for LHS" : "solving for RHS") << std::endl;

    // When we slice in order to align, we might have to reslice the one we are solving for
    bool reslice = false;

    switch (solvingFor) {
    case SOLVING_FOR_RHS: {
      concatTerms.push_back(lhsTerm);
      // Maybe we need to add more lhs to make them equal
      while (sizeDifference < 0 && !reslice) {
        Assert(lhs.size() > 0);
        // Get the next part for lhs
        lhsTerm = lhs.back();
        lhs.pop_back();
        // Slice if necessary
        if (!isSliced(lhsTerm)) {
          if (!slice(lhsTerm, lhs)) return false;
          continue;
        }
        // If we go above 0, we need to cut it
        if (sizeDifference + (int)utils::getSize(lhsTerm) > 0) {
          // Slice it so it fits
          addSlice(lhsTerm, (int)utils::getSize(lhsTerm) + sizeDifference);
          if (!slice(lhsTerm, lhs)) return false;
          if (!isSliced(rhsTerm)) {
            if (!slice(rhsTerm, rhs)) return false;
            while(!concatTerms.empty()) {
              lhs.push_back(concatTerms.back());
              concatTerms.pop_back();
            }
            reslice = true;
          }
          continue;
        }
        concatTerms.push_back(lhsTerm);
        sizeDifference += utils::getSize(lhsTerm);
      }
      break;
    }
    case SOLVING_FOR_LHS: {
      concatTerms.push_back(rhsTerm);
      // Maybe we need to add more rhs to make them equal
      while (sizeDifference > 0 && !reslice) {
        Assert(rhs.size() > 0);
        // Get the next part for lhs
        rhsTerm = rhs.back();
        rhs.pop_back();
        // Slice if necessary
        if (!isSliced(rhsTerm)) {
          if (!slice(rhsTerm, rhs)) return false;
          continue;
        }
        // If we go below 0, we need to cut it
        if (sizeDifference - (int)utils::getSize(rhsTerm) < 0) {
          // Slice it so it fits
          addSlice(rhsTerm, (int)utils::getSize(rhsTerm) - sizeDifference);
          if (!slice(rhsTerm, rhs)) return false;
	  if (!isSliced(lhsTerm)) {
            if (!slice(lhsTerm, lhs)) return false;
            while(!concatTerms.empty()) {
              rhs.push_back(concatTerms.back());
              concatTerms.pop_back();
            }
            reslice = true;
          }
          continue;
        }
        concatTerms.push_back(rhsTerm);
        sizeDifference -= utils::getSize(rhsTerm);
      }
      break;
    }
    }

    // If we need to reslice
    if (reslice) {
	continue;
    }

    Assert(sizeDifference == 0);

    Node concat = utils::mkConcat(concatTerms);
    Debug("slicing") << "SliceManager::sliceAndSolve(): concatenation " << concat << std::endl;

    // We have them equal size now. If the base term of the one we are solving is solved into a
    // non-trivial concatenation already, we have to normalize. A concatenation is non-trivial if
    // it is not a direct slicing, i.e it is a concat, and normalize(x) != x
    switch (solvingFor) {
    case SOLVING_FOR_LHS: {
      TNode lhsTermRepresentative = d_equalityEngine.getRepresentative(lhsTerm);
      if (lhsTermRepresentative != lhsTerm &&
          (lhsTermRepresentative.getKind() == kind::BITVECTOR_CONCAT || lhsTermRepresentative.getKind() == kind::CONST_BITVECTOR)) {
        // We need to normalize and solve the normalized equations
        std::vector<TNode> explanation;
        d_equalityEngine.getExplanation(lhsTerm, lhsTermRepresentative, explanation);
        std::set<TNode> additionalAssumptions(assumptions);
        additionalAssumptions.insert(explanation.begin(), explanation.end());
        bool ok = solveEquality(lhsTermRepresentative, concat, additionalAssumptions);
        if (!ok) return false;
      } else {
        // We're fine, just add the equality
        Debug("slicing") << "SliceManager::sliceAndSolve(): adding " << lhsTerm << " = " << concat << " " << utils::setToString(assumptions) << std::endl;
        d_equalityEngine.addTerm(concat);
        bool ok = d_equalityEngine.addEquality(lhsTerm, concat, utils::mkConjunction(assumptions));
        if (!ok) return false;
      }
      break;
    }
    case SOLVING_FOR_RHS: {
      TNode rhsTermRepresentative = d_equalityEngine.getRepresentative(rhsTerm);
      if (rhsTermRepresentative != rhsTerm &&
          (rhsTermRepresentative.getKind() == kind::BITVECTOR_CONCAT || rhsTermRepresentative.getKind() == kind::CONST_BITVECTOR)) {
        // We need to normalize and solve the normalized equations
        std::vector<TNode> explanation;
        d_equalityEngine.getExplanation(rhsTerm, rhsTermRepresentative, explanation);
        std::set<TNode> additionalAssumptions(assumptions);
        additionalAssumptions.insert(explanation.begin(), explanation.end());
        bool ok = solveEquality(rhsTermRepresentative, concat, additionalAssumptions);
        if (!ok) return false;
      } else {
        // We're fine, just add the equality
        Debug("slicing") << "SliceManager::sliceAndSolve(): adding " << rhsTerm << " = " << concat << utils::setToString(assumptions) << std::endl;
        d_equalityEngine.addTerm(concat);
        bool ok = d_equalityEngine.addEquality(rhsTerm, concat, utils::mkConjunction(assumptions));
        if (!ok) return false;
      }
      break;
    }
    }
  }

  return true;
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
      // The term is not sliced if one of the borders is not in the slice set or
      // there is a point between the borders      
      result = 
	d_setCollection.contains(find->second, low) && d_setCollection.contains(find->second, high + 1) &&
        (low == high || d_setCollection.count(find->second, low + 1, high) == 0);
    }
  }

  Debug("slicing") << "SliceManager::isSliced(" << node << ") => " << (result ? "true" : "false") << std::endl;
  return result;
}

template <class TheoryBitvector>
inline bool SliceManager<TheoryBitvector>::slice(TNode node, std::vector<Node>& sliced) {

  Debug("slicing") << "SliceManager::slice(" << node << ")" << std::endl;

  Assert(!isSliced(node));

  // The indices of the beginning and (one past) end
  unsigned high = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractHigh(node) + 1 : utils::getSize(node);
  unsigned low  = node.getKind() == kind::BITVECTOR_EXTRACT ? utils::getExtractLow(node) : 0;
  Debug("slicing") << "SliceManager::slice(" << node << "): low: " << low << std::endl;
  Debug("slicing") << "SliceManager::slice(" << node << "): high: " << high << std::endl;

  // Get the base term
  TNode nodeBase = baseTerm(node);
  Assert(nodeBase.getKind() != kind::BITVECTOR_CONCAT);
  Assert(nodeBase.getKind() != kind::CONST_BITVECTOR);

  // The nodes slice set
  set_collection::reference_type nodeSliceSet;

  // Find the current one or construct it
  slicing_map::iterator findSliceSet = d_nodeSlicing.find(nodeBase);
  if (findSliceSet == d_nodeSlicing.end()) {
    nodeSliceSet = d_setCollection.newSet(utils::getSize(nodeBase));
    d_setCollection.insert(nodeSliceSet, 0);
    d_nodeSlicing[nodeBase] = nodeSliceSet;
  } else {
    nodeSliceSet = d_nodeSlicing[nodeBase];
  }

  Debug("slicing") << "SliceManager::slice(" << node << "): current: " << d_setCollection.toString(nodeSliceSet) << std::endl;
  std::vector<size_t> slicePoints;
  if (low + 1 < high) {
    d_setCollection.getElements(nodeSliceSet, low + 1, high - 1, slicePoints);
  }
 
  // Go through all the points i_0 <= low < i_1 < ... < i_{n-1} < high <= i_n from the slice set
  // and generate the slices [i_0:low-1][low:i_1-1] [i_1:i2] ... [i_{n-1}:high-1][high:i_n-1]. They are in reverse order,
  // as they should be
  size_t i_0 = low == 0 ? 0 : d_setCollection.prev(nodeSliceSet, low + 1);
  Debug("slicing") << "SliceManager::slice(" << node << "): i_0: " << i_0 << std::endl;
  size_t i_n = high == utils::getSize(nodeBase) ? high: d_setCollection.next(nodeSliceSet, high - 1);
  Debug("slicing") << "SliceManager::slice(" << node << "): i_n: " << i_n << std::endl;

  // Add the new points to the slice set (they might be there already)
  if (high < i_n) {
    if (!addSlice(nodeBase, high)) return false;
  }
  // Construct the actuall slicing
  if (slicePoints.size() > 0) {
    Debug("slicing") << "SliceManager::slice(" << node << "): adding" << utils::mkExtract(nodeBase, slicePoints[0] - 1, low) << std::endl;
    sliced.push_back(utils::mkExtract(nodeBase, slicePoints[0] - 1, low));
    for (unsigned i = 1; i < slicePoints.size(); ++ i) {
      Debug("slicing") << "SliceManager::slice(" << node << "): adding" << utils::mkExtract(nodeBase, slicePoints[i] - 1, slicePoints[i-1])<< std::endl;
      sliced.push_back(utils::mkExtract(nodeBase, slicePoints[i] - 1, slicePoints[i-1]));
    }
    Debug("slicing") << "SliceManager::slice(" << node << "): adding" << utils::mkExtract(nodeBase, high-1, slicePoints.back()) << std::endl;
    sliced.push_back(utils::mkExtract(nodeBase, high-1, slicePoints.back()));
  } else {
    sliced.push_back(utils::mkExtract(nodeBase, high - 1, low));
  }
  // Add the new points to the slice set (they might be there already)
  if (i_0 < low) {
    if (!addSlice(nodeBase, low)) return false;
  }

  return true;
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

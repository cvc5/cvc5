/*********************                                                        */
/*! \file cd_set_collection.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

/*
 * set_collection.h
 *
 *  Created on: Feb 24, 2011
 *      Author: dejan
 */

#pragma once

#include "cvc4_private.h"

#include <iostream>
#include "context/cdo.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace context {

/**
 * A class representing a backtrackable set of slice points. The memory should allow indexing with the TreeEntry.left and
 * TreeEntry.right. TreeEntry should also provide null for the non-existing reference and a constructor with (value,
 * left, right).
 */
template <typename memory_type, typename tree_entry_type, typename value_type, bool pass_value_by_reference = false>
class BacktrackableSetCollection {

  /**
   * This is an interesting C++ question: how to make class applicable to non-by-value elements. If we turn
   * below into const value_type& it doesn't work for the bit-slicing as size_t it is passed by value, and moreover
   * we are using only a part of the word for the value. Hmmm.
   */
  typedef value_type const_value_reference;

  /** Type of the reference */
  typedef typename tree_entry_type::reference_type reference_type;

  /** The null reference */
  static const reference_type null = tree_entry_type::null;

  /** The memory this set collection will use */
  memory_type d_memory;

  /** Backtrackable number of nodes that have been inserted */
  context::CDO<unsigned> d_nodesInserted;

  /** Check if the reference is valid in the current context */
  inline bool isValid(reference_type set) const {
    return d_nodesInserted == d_memory.size() && (set == null || set < d_memory.size());
  }

  /** Backtrack */
  void backtrack() {
    while (d_nodesInserted < d_memory.size()) {
      const tree_entry_type& node = d_memory.back();

      if(Debug.isOn("cd_set_collection")) {
        Debug("cd_set_collection") << "BacktrackableSetCollection::backtrack(): removing " << node.getValue()
                                     << " from " << internalToString(getRoot(d_memory.size()-1)) << std::endl;
      }

      if (node.hasParent()) {
        if (node.isLeft()) {
          d_memory[node.getParent()].removeLeft();
        } else {
          d_memory[node.getParent()].removeRight();
        }
      }
      d_memory.pop_back();
    }
  }

  inline void backtrack() const {
    const_cast<BacktrackableSetCollection*>(this)->backtrack();
  }

  /**
   * Create a new set. The set must have at least one element.
   */
  reference_type newElement(const value_type& value, reference_type left, reference_type right, reference_type parent, bool isLeft) {
    reference_type index = d_memory.size();
    d_memory.push_back(tree_entry_type(value, left, right, parent, isLeft));
    d_nodesInserted = d_nodesInserted + 1;
    return index;
  }

  /**
   * Return the reference to the value if it's in the set or null otherwise
   */
  reference_type find(reference_type set, const value_type& value) const {
    while (set != null) {
      const tree_entry_type& node = d_memory[set];
      if (node.getValue() == value) {
        return set;
      } else if (value < node.getValue()) {
        set = node.getLeft();
      } else {
        set = node.getRight();
      }
    }
    return null;
  }

  /**
   * Returns the maximal value in the set
   */
  reference_type max(reference_type set) const {
    Assert(set != null);
    Assert(isValid(set));
    while (d_memory[set].hasRight()) {
      set = d_memory[set].getRight();
    }
    return set;
  }

  /**
   * Returns the minimal value in the set
   */
  reference_type min(reference_type set) const {
    Assert(set != null);
    Assert(isValid(set));
    while (d_memory[set].hasLeft()) {
      set = d_memory[set].getLeft();
    }
    return set;
  }

  /**
   * REturns the root of the tree
   */
  reference_type getRoot(reference_type set) const {
    // We don't check validity as this is used in backtracking
    while (set != null && d_memory[set].hasParent()) {
      Assert(set > d_memory[set].getParent());
      set = d_memory[set].getParent();
    }
    return set;
  }

  /**
   * Print the list of elements to the output.
   */
  void internalPrint(std::ostream& out, reference_type set) const {
    if (set == null) {
      return;
    }
    const tree_entry_type& current = d_memory[set];
    if (current.hasLeft()) {
      internalPrint(out, current.getLeft());
      out << ",";
    }
    out << current.getValue();
    if (current.hasRight()) {
      out << ",";
      internalPrint(out, current.getRight());
    }
  }

  /**
   * String representation of a set.
   */
  std::string internalToString(reference_type set) const {
    std::stringstream out;
    internalPrint(out, set);
    return out.str();
  }


public:

  BacktrackableSetCollection(context::Context* context)
  : d_nodesInserted(context, 0) {}

  size_t size() const {
    backtrack();
    return d_memory.size();
  }

  size_t size(reference_type set) const {
    backtrack();
    Assert(isValid(set));
    if (set == null) return 0;
    size_t n = 1;
    if (d_memory[set].hasLeft()) {
      n += size(d_memory[set].getLeft());
    }
    if (d_memory[set].hasRight()) {
      n += size(d_memory[set].getRight());
    }
    return n;
  }

  reference_type newSet(const value_type& value) {
    backtrack();
    return newElement(value, null, null, null, false);
  }

  void insert(reference_type& root, const value_type& value) {
    backtrack();
    Assert(isValid(root));
    if (root == null) {
      root = newSet(value);
      return;
    }
    // We already have a set, find the spot
    reference_type parent = null;
    reference_type current = root;
    while (true) {
      Assert(isValid(current));
      if (value < d_memory[current].getValue()) {
        if (d_memory[current].hasLeft()) {
          parent = current;
          current = d_memory[current].getLeft();
        } else {
          d_memory[current].setLeft(newElement(value, null, null, current, true));
          Assert(d_memory[current].hasLeft());
          return;
        }
      } else {
        Assert(value != d_memory[current].getValue());
        if (d_memory[current].hasRight()) {
          parent = current;
          current = d_memory[current].getRight();
        } else {
          d_memory[current].setRight(newElement(value, null, null, current, false));
          Assert(d_memory[current].hasRight());
          return;
        }
      }
    }
  }

  /**
   * Returns the maximal value in the set
   */
  const_value_reference maxElement(reference_type set) const {
    Assert(set != null);
    Assert(isValid(set));
    backtrack();
    return d_memory[max(set)].getValue();
  }

  /**
   * Returns the minimal value in the set
   */
  const_value_reference minElement(reference_type set) const {
    Assert(set != null);
    Assert(isValid(set));
    backtrack();
    return d_memory[min(set)].getValue();
  }

  /**
   * Return the previous (smaller) element.
   */
  const_value_reference prev(reference_type set, const_value_reference value) {
    backtrack();
    Assert(isValid(set));

    const_value_reference candidate_value = value_type();
    bool candidate_found = false;

    // Find the biggest node smaleer than value (it must exist)
    while (set != null) {
      if(Debug.isOn("set_collection")) {
        Debug("set_collection") << "BacktrackableSetCollection::getPrev(" << toString(set) << "," << value << ")" << std::endl;
      }
      const tree_entry_type& node = d_memory[set];
      if (node.getValue() >= value) {
        // If the node is bigger than the value, we need a smaller one
        set = node.getLeft();
      } else {
        // The node is smaller than the value
        candidate_found = true;
        candidate_value = node.getValue();
        // There might be a bigger one
        set = node.getRight();
      }
    }

    Assert(candidate_found);
    return candidate_value;
  }

  const_value_reference next(reference_type set, const_value_reference value) {
    backtrack();
    Assert(isValid(set));

    const_value_reference candidate_value = value_type();
    bool candidate_found = false;

    // Find the smallest node bigger than value (it must exist)
    while (set != null) {
      if(Debug.isOn("set_collection")) {
        Debug("set_collection") << "BacktrackableSetCollection::getNext(" << toString(set) << "," << value << ")" << std::endl;
      }
      const tree_entry_type& node = d_memory[set];
      if (node.getValue() <= value) {
        // If the node is smaller than the value, we need a bigger one
        set = node.getRight();
      } else {
        // The node is bigger than the value
        candidate_found = true;
        candidate_value = node.getValue();
        // There might be a smaller one
        set = node.getLeft();
      }
    }

    Assert(candidate_found);
    return candidate_value;
}

  /**
   * Count the number of elements in the given bounds.
   */
  unsigned count(reference_type set, const_value_reference lowerBound, const_value_reference upperBound) const {
    Assert(lowerBound <= upperBound);
    backtrack();
    Assert(isValid(set));

    // Empty set no elements
    if (set == null) {
      return 0;
    }
    // The counter
    unsigned c = 0;
    // Current set
    const tree_entry_type& current = d_memory[set];
    // Left child (smaller elements)
    if (lowerBound < current.getValue()) {
      c += count(current.getLeft(), lowerBound, upperBound);
    }
    // Current element
    if (lowerBound <= current.getValue() && current.getValue() <= upperBound) {
      ++ c;
    }
    // Right child (bigger elements)
    if (current.getValue() <= upperBound) {
      c += count(current.getRight(), lowerBound, upperBound);
    }
    return c;
  }

  /**
   * Check for membership.
   */
  bool contains(reference_type set, const_value_reference value) const {
    backtrack();
    Assert(isValid(set));
    return count(set, value, value) > 0;
  }

  /**
   * Returns the elements (sorted) in the set between the given lower and upper bound. If include borders is on,
   * and the
   */
  void getElements(reference_type set, const_value_reference lowerBound, const_value_reference upperBound, std::vector<value_type>& output) const {
    Assert(lowerBound <= upperBound);
    backtrack();
    Assert(isValid(set));

    if(Debug.isOn("set_collection")) {
      Debug("set_collection") << "BacktrackableSetCollection::getElements(" << toString(set) << "," << lowerBound << "," << upperBound << ")" << std::endl;
    }

    // Empty set no elements
    if (set == null) {
      return;
    }
    // Current set
    const tree_entry_type& current = d_memory[set];
    // Left child (smaller elements)
    if (lowerBound < current.getValue()) {
      getElements(current.getLeft(), lowerBound, upperBound, output);
    }
    // Current element
    if (lowerBound <= current.getValue() && current.getValue() <= upperBound) {
      output.push_back(current.getValue());
    }
    // Right child (bigger elements)
    if (current.getValue() < upperBound) {
      getElements(current.getRight(), lowerBound, upperBound, output);
    }
  }

  /**
   * Print the list of elements to the output.
   */
  void print(std::ostream& out, reference_type set) const {
    backtrack();
    Assert(isValid(set));

    if (set == null) {
      return;
    }
    const tree_entry_type& current = d_memory[set];
    if (current.hasLeft()) {
      print(out, current.getLeft());
      out << ",";
    }
    out << current.getValue();
    if (current.hasRight()) {
      out << ",";
      print(out, current.getRight());
    }
  }

  /**
   * String representation of a set.
   */
  std::string toString(reference_type set) const {
    backtrack();
    Assert(isValid(set));

    std::stringstream out;
    print(out, set);
    return out.str();
  }
};

} // Namespace context
} // Namespace CVC4s

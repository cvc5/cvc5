/*
 * set_collection.h
 *
 *  Created on: Feb 24, 2011
 *      Author: dejan
 */

#pragma once

#include <iostream>
#include "context/cdo.h"

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

  /** Backtrack */
  void backtrack() {
    while (d_nodesInserted < d_memory.size()) {
      const tree_entry_type& node = d_memory.back();
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
    d_memory.push_back(tree_entry_type(value, left, right, value, isLeft));
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
    while (d_memory[set].hasLeft()) {
      set = d_memory[set].getLeft();
    }
    return set;
  }

public:

  BacktrackableSetCollection(context::Context* context)
  : d_nodesInserted(context, 0) {}

  size_t size() const {
    backtrack();
    return d_memory.size();
  }

  reference_type newSet(const value_type& value) {
    backtrack();
    return newElement(value, null, null, null, false);
  }

  void insert(memory_type& memory, reference_type root, const value_type& value) {
    backtrack();
    if (root == null) {
      return newSet(value);
    }
    // We already have a set, find the spot
    reference_type parent = null;
    while (true) {
      parent = root;
      if (value < d_memory[root].value) {
        root = d_memory[root].left;
        if (root == null) {
          root = newElement(value, null, null, parent, true);
          d_memory[parent].left = root;
          return;
        }
      } else {
        Assert(value != d_memory[root].value);
        root = d_memory[root].right;
        if (root == null) {
          root = newElement(value, null, null, parent, false);
          d_memory[parent].right = root;
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
    backtrack();
    return d_memory[max(set)].getValue();
  }

  /**
   * Returns the minimal value in the set
   */
  const_value_reference minElement(reference_type set) const {
    Assert(set != null);
    backtrack();
    return d_memory[min(set)].getValue();
  }

  /**
   * Return the previous (smaller) element.
   */
  const_value_reference prev(reference_type set, const_value_reference value) {
    backtrack();
    // Get the node of this value
    reference_type node_ref = find(set, value);
    Assert(node_ref != null);
    const tree_entry_type& node = d_memory[node_ref];
    // For a left node, we know that it is smaller than all the parents and the parents other children
    // The smaller node must then be the max of the left subtree
    if (!node.hasParent() || node.isLeft()) {
      return maxElement(node.getLeft());
    }
    // For a right node, we know that it is bigger than the parent. But, we also know that the left subtree
    // is also bigger than the parent
    else {
      if (node.hasLeft()) {
        return maxElement(node.getLeft());
      } else {
        Assert(node.hasParent());
        return d_memory[node.getParent()].getValue();
      }
    }
  }

  const_value_reference next(reference_type set, const_value_reference value) {
    backtrack();
    // Get the node of this value
    reference_type node_ref = find(set, value);
    Assert(node_ref != null);
    const tree_entry_type& node = d_memory[node_ref];
    // For a right node, we know that it is bigger than all the parents and the parents other children
    // The bigger node must then be the min of the right subtree
    if (!node.hasParent() || node.isRight()) {
      return minElement(node.getRight());
    }
    // For a left node, we know that it is smaller than the parent. But, we also know that the right subtree
    // is also smaller than the parent
    else {
      if (node.hasRight()) {
        return minElement(node.getRight());
      } else {
        Assert(node.hasParent());
        return d_memory[node.getParent()].getValue();
      }
    }
  }

  /**
   * Count the number of elements in the given bounds.
   */
  unsigned count(reference_type set, const_value_reference lowerBound, const_value_reference upperBound) const {
    Assert(lowerBound <= upperBound);
    backtrack();
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
    return count(set, value, value) > 0;
  }

  /**
   * Returns the elements (sorted) in the set between the given lower and upper bound. If include borders is on,
   * and the
   */
  void getElements(reference_type set, const_value_reference lowerBound, const_value_reference upperBound, std::vector<value_type>& output) const {
    Assert(lowerBound <= upperBound);
    backtrack();
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
    if (current.getValue() <= upperBound) {
      getElements(current.getRight(), lowerBound, upperBound, output);
    }
  }

  /**
   * Print the list of elements to the output.
   */
  void print(std::ostream& out, reference_type set) {
    backtrack();
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
  std::string toString(reference_type set) {
    std::stringstream out;
    print(out, set);
    return out.str();
  }
};

} // Namespace context
} // Namespace CVC4s

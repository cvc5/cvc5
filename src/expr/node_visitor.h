/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple visitor for nodes.
 */

#pragma once

#include <vector>

#include "cvc5_private.h"
#include "expr/node.h"

namespace cvc5::internal {

/**
 * Traverses the nodes reverse-topologically (children before parents),
 * calling the visitor in order.
 */
template<typename Visitor>
class NodeVisitor {

public:

  /**
   * Element of the stack.
   */
  struct stack_element {
    /** The node to be visited */
    TNode d_node;
    /** The parent of the node */
    TNode d_parent;
    /** Have the children been queued up for visitation */
    bool d_childrenAdded;
    stack_element(TNode node, TNode parent)
        : d_node(node), d_parent(parent), d_childrenAdded(false)
    {
    }
  };/* struct preprocess_stack_element */

  /**
   * Performs the traversal.
   */
  static typename Visitor::return_type run(Visitor& visitor, TNode node) {

    // Notify of a start
    visitor.start(node);

    // Do a reverse-topological sort of the subexpressions
    std::vector<stack_element> toVisit;
    toVisit.push_back(stack_element(node, node));
    while (!toVisit.empty()) {
      stack_element& stackHead = toVisit.back();
      // The current node we are processing
      TNode current = stackHead.d_node;
      TNode parent = stackHead.d_parent;

      if (visitor.alreadyVisited(current, parent)) {
        // If already visited, we're done
        toVisit.pop_back();
      }
      else if (stackHead.d_childrenAdded)
      {
        // Call the visitor
        visitor.visit(current, parent);
        // Done with this node, remove from the stack
        toVisit.pop_back();
      }
      else
      {
        // Mark that we have added the children
        stackHead.d_childrenAdded = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          if (!visitor.alreadyVisited(childNode, current)) {
            toVisit.push_back(stack_element(childNode, current));
          }
        }
      }
    }

    // Notify that we're done
    return visitor.done(node);
  }

};/* class NodeVisitor<> */

}  // namespace cvc5::internal

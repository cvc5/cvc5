/*********************                                                        */
/*! \file node_visitor.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A simple visitor for nodes.
 **
 ** The theory engine.
 **/

#pragma once

#include "cvc4_private.h"

#include <vector>
#include "expr/node.h"

namespace CVC4 {

/**
 * Traverses the nodes topologically and call the visitor when all the children have been visited.
 */
template<typename Visitor>
class NodeVisitor {

public:

  /**
   * Element of the stack.
   */
  struct stack_element {
    /** The node to be visited */
    TNode node;
    /** The parent of the node */
    TNode parent;
    /** Have the children been queued up for visitation */
    bool children_added;
    stack_element(TNode node, TNode parent)
    : node(node), parent(parent), children_added(false) {}
  };/* struct preprocess_stack_element */

  /**
   * Performs the traversal.
   */
  static typename Visitor::return_type run(Visitor& visitor, TNode node) {

    // Notify of a start
    visitor.start(node);

    // Do a topological sort of the subexpressions
    std::vector<stack_element> toVisit;
    toVisit.push_back(stack_element(node, node));
    while (!toVisit.empty()) {
      stack_element& stackHead = toVisit.back();
      // The current node we are processing
      TNode current = stackHead.node;
      TNode parent = stackHead.parent;

      if (visitor.alreadyVisited(current, parent)) {
        // If already visited, we're done
        toVisit.pop_back();
      } else if (stackHead.children_added) {
        // Call the visitor
        visitor.visit(current, parent);
        // Done with this node, remove from the stack
        toVisit.pop_back();
      } else {
        // Mark that we have added the children
        stackHead.children_added = true;
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

};

}


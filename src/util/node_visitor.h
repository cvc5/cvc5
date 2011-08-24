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
template<typename Visitor, typename VisitedAttribute>
class NodeVisitor {

public:

  /**
   * Element of the stack.
   */
  struct stack_element {
    /** The node to be visited */
    TNode node;
    bool children_added;
    stack_element(TNode node)
    : node(node), children_added(false) {}
  };/* struct preprocess_stack_element */

  /**
   * Performs the traversal.
   */
  static void run(Visitor visitor, TNode node) {
    // If the node has been visited already, we're done
    if (node.getAttribute(VisitedAttribute())) {
      return;
    }
    // Do a topological sort of the subexpressions and preregister them
    std::vector<stack_element> toVisit;
    toVisit.push_back((TNode) node);
    while (!toVisit.empty()) {
      stack_element& stackHead = toVisit.back();
      // The current node we are processing
      TNode current = stackHead.node;

      if (current.getAttribute(VisitedAttribute())) {
        // If already visited, we're done
        toVisit.pop_back();
      } else if (stackHead.children_added) {
        // If children have been processed, we can visit the current
        current.setAttribute(VisitedAttribute(), true);
        // Call the visitor
        visitor(current);
        // Done with this node, remove from the stack
        toVisit.pop_back();
      } else {
        // Mark that we have added the children
        stackHead.children_added = true;
        // We need to add the children
        for(TNode::iterator child_it = current.begin(); child_it != current.end(); ++ child_it) {
          TNode childNode = *child_it;
          if (!childNode.getAttribute(VisitedAttribute())) {
            toVisit.push_back(childNode);
          }
        }
      }
    }

  }

};

}


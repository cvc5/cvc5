/*********************                                                        */
/*! \file node_algorithm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common algorithms on nodes
 **
 ** This file implements common algorithms applied to nodes, such as checking if
 ** a node contains a free or a bound variable. This file should generally only
 ** be included in source files.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__NODE_ALGORITHM_H
#define __CVC4__EXPR__NODE_ALGORITHM_H

#include <unordered_map>
#include <vector>

#include "expr/node.h"

namespace CVC4 {
namespace expr {

/**
 * Check if the node n has a subterm t.
 * @param n The node to search in
 * @param t The subterm to search for
 * @param strict If true, a term is not considered to be a subterm of itself
 * @return true iff t is a subterm in n
 */
bool hasSubterm(TNode n, TNode t, bool strict = false);

/**
 * Check if the node n has >1 occurrences of a subterm t.
 */
bool hasSubtermMulti(TNode n, TNode t);

/**
 * Returns true iff the node n contains a bound variable, that is a node of
 * kind BOUND_VARIABLE. This bound variable may or may not be free.
 * @param n The node under investigation
 * @return true iff this node contains a bound variable
 */
bool hasBoundVar(TNode n);

/**
 * Returns true iff the node n contains a free variable, that is, a node
 * of kind BOUND_VARIABLE that is not bound in n.
 * @param n The node under investigation
 * @return true iff this node contains a free variable.
 */
bool hasFreeVar(TNode n);

/**
 * For term n, this function collects the symbols that occur as a subterms
 * of n. A symbol is a variable that does not have kind BOUND_VARIABLE.
 * @param n The node under investigation
 * @param syms The set which the symbols of n are added to
 */
void getSymbols(TNode n, std::unordered_set<Node, NodeHashFunction>& syms);
/** Same as above, with a visited cache */
void getSymbols(TNode n,
                std::unordered_set<Node, NodeHashFunction>& syms,
                std::unordered_set<TNode, TNodeHashFunction>& visited);

}  // namespace expr
}  // namespace CVC4

#endif

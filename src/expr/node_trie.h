/*********************                                                        */
/*! \file node_trie.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term_arg_trie
 **/

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__NODE_TRIE_H
#define __CVC4__EXPR__NODE_TRIE_H

#include <map>
#include "expr/node.h"

namespace CVC4 {
namespace theory {


/** TNode trie class
*
* This is a trie data structure whose distinguish feature is that it has
* references to children only and no "data" members, for the sake of efficiency.
* 
* One use of this class is to represent "term indices" or a "signature tables",
* for symbols with fixed arities. In this case, we "index" terms by the list
* of representatives of their arguments.
*
* For example, consider the equivalence classes :
*
* { a, d, f( d, c ), f( a, c ) }
* { b, f( b, d ) }
* { c, f( b, b ) }
*
* where the first elements ( a, b, c ) are the representatives of these classes.
* The TNodeTrie t we may build for f is :
*
* t :
*   t.d_data[a] :
*     t.d_data[a].d_data[c] :
*       t.d_data[a].d_data[c].d_data[f(d,c)] : (leaf)
*   t.d_data[b] :
*     t.d_data[b].d_data[b] :
*       t.d_data[b].d_data[b].d_data[f(b,b)] : (leaf)
*     t.d_data[b].d_data[d] :
*       t.d_data[b].d_data[d].d_data[f(b,d)] : (leaf)
*
* Leaf nodes store the terms that are indexed by the arguments, for example
* term f(d,c) is indexed by the representative arguments (a,c), and is stored
* as a the (single) key in the data of t.d_data[a].d_data[c].
*/
class TNodeTrie {
 public:
  /** the data */
  std::map< TNode, TNodeTrie > d_data;
  /** for leaf nodes : does this trie have data? */
  bool hasNodeData() { return !d_data.empty(); }
  /** for leaf nodes : get term corresponding to this leaf */
  TNode getNodeData() { return d_data.begin()->first; }
  /** 
  * Returns the term that is indexed by reps, if one exists, or
  * or returns null otherwise.
  */
  TNode existsTerm(std::vector<TNode>& reps);
  /**
  * Returns the term that is previously indexed by reps, if one exists, or
  * Adds n to the trie, indexed by reps, and returns n.
  */
  TNode addOrGetTerm(TNode n, std::vector<TNode>& reps);
  /** 
  * Returns false if a term is previously indexed by reps.
  * Returns true if no term is previously indexed by reps,
  *   and adds n to the trie, indexed by reps, and returns n.
  */
  bool addTerm(TNode n, std::vector<TNode>& reps);
  /** debug print this trie */
  void debugPrint(const char* c, Node n, unsigned depth = 0);
  /** clear all data from this trie */
  void clear() { d_data.clear(); }
  /** is empty */
  bool empty() { return d_data.empty(); }
};/* class TNodeTrie */

} /* CVC4::theory namespace */
} /* CVC4 namespace */

#endif /* __CVC4__EXPR__NODE_TRIE_H */

/*********************                                                        */
/*! \file node_trie.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A trie class for Nodes and TNodes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__NODE_TRIE_H
#define CVC4__EXPR__NODE_TRIE_H

#include <map>
#include "expr/node.h"

namespace CVC4 {
namespace theory {

/** NodeTemplate trie class
 *
 * This is a trie data structure whose distinguishing feature is that it has
 * no "data" members and only references to children. The motivation for having
 * no data members is efficiency.
 *
 * One use of this class is to represent "term indices" or a "signature tables"
 * for symbols with fixed arities. In this use case, we "index" terms by the
 * list of representatives of their arguments.
 *
 * For example, consider the equivalence classes :
 *
 * { a, d, f( d, c ), f( a, c ) }
 * { b, f( b, d ) }
 * { c, f( b, b ) }
 *
 * where the first elements ( a, b, c ) are the representatives of these
 * classes. The NodeTemplateTrie t we may build for f is :
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
template <bool ref_count>
class NodeTemplateTrie
{
 public:
  /** The children of this node. */
  std::map<NodeTemplate<ref_count>, NodeTemplateTrie<ref_count>> d_data;
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_data.empty(); }
  /** For leaf nodes : get the node corresponding to this leaf. */
  NodeTemplate<ref_count> getData() const { return d_data.begin()->first; }
  /**
   * Returns the term that is indexed by reps, if one exists, or
   * or returns null otherwise.
   */
  NodeTemplate<ref_count> existsTerm(
      const std::vector<NodeTemplate<ref_count>>& reps) const;
  /**
   * Returns the term that is previously indexed by reps, if one exists, or
   * adds n to the trie, indexed by reps, and returns n.
   */
  NodeTemplate<ref_count> addOrGetTerm(
      NodeTemplate<ref_count> n,
      const std::vector<NodeTemplate<ref_count>>& reps);
  /**
   * Returns false if a term is previously indexed by reps.
   * Returns true if no term is previously indexed by reps,
   *   and adds n to the trie, indexed by reps.
   */
  inline bool addTerm(NodeTemplate<ref_count> n,
                      const std::vector<NodeTemplate<ref_count>>& reps);
  /** Debug print this trie on Trace c with indentation depth. */
  void debugPrint(const char* c, unsigned depth = 0) const;
  /** Clear all data from this trie. */
  void clear() { d_data.clear(); }
  /** Is this trie empty? */
  bool empty() const { return d_data.empty(); }
}; /* class NodeTemplateTrie */

template <bool ref_count>
bool NodeTemplateTrie<ref_count>::addTerm(
    NodeTemplate<ref_count> n, const std::vector<NodeTemplate<ref_count>>& reps)
{
  return addOrGetTerm(n, reps) == n;
}

/** Reference-counted version of the above data structure */
typedef NodeTemplateTrie<true> NodeTrie;
/** Non-reference-counted version of the above data structure */
typedef NodeTemplateTrie<false> TNodeTrie;

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__EXPR__NODE_TRIE_H */

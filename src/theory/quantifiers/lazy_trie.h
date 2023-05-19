/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lazy trie.
 */

#ifndef CVC5__THEORY__QUANTIFIERS__LAZY_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__LAZY_TRIE_H

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** abstract evaluator class
 *
 * This class is used for the LazyTrie data structure below.
 */
class LazyTrieEvaluator
{
 public:
  virtual ~LazyTrieEvaluator() {}
  virtual Node evaluate(Node n, unsigned index) = 0;
};

/** LazyTrie
 *
 * This is a trie where terms are added in a lazy fashion. This data structure
 * is useful, for instance, when we are only interested in when two terms
 * map to the same node in the trie but we need not care about computing
 * exactly where they are.
 *
 * In other words, when a term n is added to this trie, we do not insist
 * that n is placed at the maximal depth of the trie. Instead, we place n at a
 * minimal depth node that has no children. In this case we say n is partially
 * evaluated in this trie.
 *
 * This class relies on an abstract evaluator interface above, which evaluates
 * nodes for indices.
 *
 * For example, say we have terms a, b, c and an evaluator ev where:
 *   ev->evaluate( a, 0,1,2 ) = 0, 5, 6
 *   ev->evaluate( b, 0,1,2 ) = 1, 3, 0
 *   ev->evaluate( c, 0,1,2 ) = 1, 3, 2
 * After adding a to the trie, we get:
 *   root: a
 * After adding b to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: b
 * After adding c to the resulting trie, we get:
 *   root: null
 *     d_children[0]: a
 *     d_children[1]: null
 *       d_children[3]: null
 *         d_children[0] : b
 *         d_children[2] : c
 * Notice that we need not call ev->evalute( a, 1 ) and ev->evalute( a, 2 ).
 */
class LazyTrie
{
 public:
  LazyTrie() {}
  ~LazyTrie() {}
  /** the data at this node, which may be partially evaluated */
  Node d_lazy_child;
  /** the children of this node */
  std::map<Node, LazyTrie> d_children;
  /** clear the trie */
  void clear() { d_children.clear(); }
  /** add n to the trie
   *
   * This function returns a node that is mapped to the same node in the trie
   * if one exists, or n otherwise.
   *
   * ev is an evaluator which determines where n is placed in the trie
   * index is the depth of this node
   * ntotal is the maximal depth of the trie
   * forceKeep is whether we wish to force that n is chosen as a representative
   */
  Node add(Node n,
           LazyTrieEvaluator* ev,
           unsigned index,
           unsigned ntotal,
           bool forceKeep);
};

using IndTriePair = std::pair<unsigned, LazyTrie*>;

/** Lazy trie with multiple elements per leaf
 *
 * As the above trie, but allows multiple elements per leaf. This is done by
 * keeping classes of elements associated with each element kept in a leaf,
 * which is denoted the representative of the class associated with that leaf.
 *
 * Another feature of this data structure is to allow the insertion of new
 * classifiers besides that of data.
 */
class LazyTrieMulti
{
 public:
  /** maps representatives to their classes
   *
   * the equivalence relation is defined in terms of the tuple of evaluations
   * under the current classifiers. For example if we currently have three
   * classifiers and four elements -- a,b,c,d -- have been inserted into the
   * trie such that their evaluation on the classifiers are:
   *
   * a -> (0, 0, 0)
   * b -> (1, 3, 0)
   * c -> (1, 3, 0)
   * d -> (1, 3, 0)
   *
   * then a is the representative of the class {a}, while b of the class {b,c,d}
    */
  std::map<Node, std::vector<Node>> d_rep_to_class;
  /** adds a new classifier to the trie
   *
   * When a new classifier is added a new level is added to each leaf that has
   * data and the class associated with the element is the leaf is separated
   * according to the new classifier.
   *
   * For example in the following trie with three classifiers:
   *
   *   root: null
   *     d_children[0]: a -> {a}
   *     d_children[1]: null
   *       d_children[3]: null
   *         d_children[0] : b -> {b, c, d}
   *
   * to which we add a fourth classifier C such that C(b) = 0, C(c) = 1, C(d) =
   * 1 we have the resulting trie:
   *
   *   root: null
   *     d_children[0]: a -> {a}
   *     d_children[1]: null
   *       d_children[3]: null
   *         d_children[0] : null
   *           d_children[0] : b -> {b}
   *           d_children[1] : c -> {c, d}
   *
   * ntotal is the number of classifiers before the addition of the new one. In
   * the above example it would be 3.
   */
  void addClassifier(LazyTrieEvaluator* ev, unsigned ntotal);
  /** adds an element to the trie
   *
   * If f ends it in a leaf that already contains an element, it is added to the
   * class of that element. Otherwise it becomes the representative of the class
   * containing only itself.
   */
  Node add(Node f, LazyTrieEvaluator* ev, unsigned ntotal);
  /** clear the trie */
  void clear();

  /** A regular lazy trie */
  LazyTrie d_trie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__LAZY_TRIE_H */

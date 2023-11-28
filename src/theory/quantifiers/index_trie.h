/******************************************************************************
 * Top contributors (to current version):
 *   Mikolas Janota, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a trie that store subsets of tuples of term indices
 * that are not yielding  useful instantiations. of quantifier instantiation.
 * This is used in the term_tuple_enumerator.
 */
#ifndef CVC5__THEORY__QUANTIFIERS__INDEX_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__INDEX_TRIE_H

#include <algorithm>
#include <utility>
#include <vector>

#include "base/check.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/** A single node of the IndexTrie. */
struct IndexTrieNode
{
  std::vector<std::pair<Node, IndexTrieNode*>> d_children;
  IndexTrieNode* d_blank = nullptr;
};

/** Trie of Nodes, used to check for subsequence membership.
 *
 * The data structure stores tuples of indices where some elements may be
 * left blank. The objective is to enable checking whether a given, completely
 * filled in, tuple has a  sub-tuple  present in the data structure.  This is
 * used in the term tuple enumeration (term_tuple_enumerator.cpp) to store
 * combinations of terms that had yielded a useless instantiation  and therefore
 * should not be repeated.  Hence, we are always assuming that all tuples have
 * the same number of elements.
 *
 * So for instance, if the data structure contains (_, 1, _, 3),  any  given
 * tuple that contains 1 and 3 on second and forth position, respectively, would
 * match.
 *
 * The data structure behaves essentially as a traditional trie. Each tuple
 * is treated as a sequence of integers with a special symbol for blank, which
 * is in fact stored  in a special  child (member d_blank).  As a small
 * optimization, a suffix containing only blanks is represented by  the empty
 * subtree, i.e., a null pointer.
 *
 * Additionally, this class accepts membership queries involving null nodes,
 * which are interpreted as requiring that all possible values of the node at
 * that position are contained. For example, writing `_` for null:
 * (_, 1, 2, 3) is contained in (_, 1, _, 3)
 * (1, 1, _, 3) is contained in (_, 1, _, 3)
 * (_, 2, _, _) is not contained in (_, 1, _, 3)
 * (_, 1, 2, 3) is not contained in (0, 1, _, 3)
 */
class IndexTrie
{
 public:
  /*  Construct the trie,  if the argument ignoreFullySpecified is true,
   *  the data structure will  store only data structure containing at least
   *  one blank. */
  IndexTrie(bool ignoreFullySpecified = true)
      : d_ignoreFullySpecified(ignoreFullySpecified),
        d_root(new IndexTrieNode())
  {
  }

  virtual ~IndexTrie() { freeRec(d_root); }

  /**  Add a tuple of values into the trie  masked by a bitmask, i.e.\ position
   * i is considered blank iff mask[i] is false. */
  void add(const std::vector<bool>& mask, const std::vector<Node>& values);

  /** Check if the given set of indices is subsumed by something present in the
   * trie. If it is subsumed, give the maximum non-blank index. */
  bool find(const std::vector<Node>& members,
            /*out*/ size_t& nonBlankLength) const
  {
    nonBlankLength = 0;
    return findRec(d_root, 0, members, nonBlankLength);
  }

 private:
  /**  ignore tuples with no blanks in the add method */
  const bool d_ignoreFullySpecified;
  /**  the root of the trie, becomes null, if all tuples should match */
  IndexTrieNode* d_root;

  /** Auxiliary recursive function for cleanup. */
  void freeRec(IndexTrieNode* n);

  /** Auxiliary recursive function for finding  subsuming tuple. */
  bool findRec(const IndexTrieNode* n,
               size_t index,
               const std::vector<Node>& members,
               size_t& nonBlankLength) const;

  /** Add master values  starting from index  to a given subtree. The
   * cardinality represents the number of non-blank elements left. */
  IndexTrieNode* addRec(IndexTrieNode* n,
                        size_t index,
                        size_t cardinality,
                        const std::vector<bool>& mask,
                        const std::vector<Node>& values);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
#endif /* THEORY__QUANTIFIERS__INDEX_TRIE_H */

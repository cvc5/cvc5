/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements an n-ary match trie
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__NARY_MATCH_TRIE_H
#define CVC5__EXPR__NARY_MATCH_TRIE_H

#include <map>
#include <vector>

#include "expr/match_trie.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace expr {

/**
 * A trie used for matching n-ary terms. We use the null node as a terminator
 * when adding terms to this trie to signify the end of n-ary symbols.
 *
 * For example:
 * Adding the terms (or a b c), (or a b), (or a a) would create this index:
 *
 * OR
 *   a
 *     a
 *       null -> (or a a)
 *     b
 *       c
 *         null -> (or a b c)
 *       null -> (or a b)
 */
class NaryMatchTrie
{
 public:
  /** Get matches
   *
   * This calls ntm->notify( n, s, vars, subs ) for each term s stored in this
   * trie that is matchable with n where s = n * { vars -> subs } for some
   * vars, subs, where * has list semantics for substitution (see
   * listSubstitute in expr/nary_term_util.h).
   *
   * This function returns false if one of these calls to notify
   * returns false.
   */
  bool getMatches(Node n, NotifyMatch* ntm) const;
  /** Adds node n to this trie */
  void addTerm(Node n);
  /** Clear this trie */
  void clear();
  /** debug print */
  std::string debugPrint() const;

 private:
  /**
   * The children of this node in the trie. Terms t are indexed by a
   * depth-first (right to left) traversal on its subterms, where the
   * top-symbol of t is indexed by:
   * - operator, if t has an operator, or
   * - t, if t does not have an operator
   * Additionally we use "null" to mark the end of applications of n-ary
   * symbols.
   */
  std::map<Node, NaryMatchTrie> d_children;
  /** The set of variables in the domain of d_children */
  std::vector<Node> d_vars;
  /** The data of this node in the trie */
  Node d_data;
};

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_FILTER_H */

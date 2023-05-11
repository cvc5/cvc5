/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements a match trie, also known as a discrimination tree.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__MATCH_TRIE_H
#define CVC5__EXPR__MATCH_TRIE_H

#include <map>
#include <vector>

#include "expr/node.h"

namespace cvc5::internal {
namespace expr {

/** A virtual class for notifications regarding matches. */
class NotifyMatch
{
 public:
  virtual ~NotifyMatch() {}
  /**
   * A notification that s is equal to n * { vars -> subs }. This function
   * should return false if we do not wish to be notified of further matches.
   */
  virtual bool notify(Node s,
                      Node n,
                      std::vector<Node>& vars,
                      std::vector<Node>& subs) = 0;
};

/**
 * A trie (discrimination tree) storing a set of terms S, that can be used to
 * query, for a given term t, all terms s from S that are matchable with t,
 * that is s*sigma = t for some substitution sigma.
 */
class MatchTrie
{
 public:
  /** Get matches
   *
   * This calls ntm->notify( n, s, vars, subs ) for each term s stored in this
   * trie that is matchable with n where s = n * { vars -> subs } for some
   * vars, subs. This function returns false if one of these calls to notify
   * returns false.
   */
  bool getMatches(Node n, NotifyMatch* ntm);
  /** Adds node n to this trie */
  void addTerm(Node n);
  /** Clear this trie */
  void clear();

 private:
  /**
   * The children of this node in the trie. Terms t are indexed by a
   * depth-first (right to left) traversal on its subterms, where the
   * top-symbol of t is indexed by:
   * - (operator, #children) if t has an operator, or
   * - (t, 0) if t does not have an operator.
   */
  std::map<Node, std::map<unsigned, MatchTrie> > d_children;
  /** The set of variables in the domain of d_children */
  std::vector<Node> d_vars;
  /** The data of this node in the trie */
  Node d_data;
};

}  // namespace expr
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__CANDIDATE_REWRITE_FILTER_H */

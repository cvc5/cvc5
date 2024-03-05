/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sygus grammar reduction.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H

#include <unordered_set>

#include "expr/node.h"
#include "expr/sygus_grammar.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbSygus;

/** SygusGrammarReduce
 *
 * This class minimizes the production rules of a sygus grammar based on
 * dropping production rules whose terms are alpha-equivalent to others.
 */
class SygusGrammarReduce : protected EnvObj
{
 public:
  SygusGrammarReduce(Env& env) : EnvObj(env) {}
  ~SygusGrammarReduce() {}
  /**
   * Minimize and update non-terminal ntsym of grammar g, which drops a
   * subset of the rules of ntsym in g that can be shown not to contribute
   * any semantically unique terms to the enumeration.
   */
  void minimize(SygusGrammar& g, const Node& ntsym);
  /** Minimize and update all non-terminals of grammar g. */
  void minimize(SygusGrammar& g);

 private:
  /** get generic list
   *
   * This function constructs all well-typed variants of a term of the form
   *    op( x1, ..., xn )
   * where op is the builtin operator for dt[c], and xi = pre[i] for i=1,...,n.
   *
   * It constructs a list of terms of the form g * sigma, where sigma
   * is an automorphism on { x1...xn } such that for all xi -> xj in sigma,
   * the type for arguments i and j of dt[c] are the same. We store this in
   * the returned set.
   *
   * This function recurses on the arguments of r, index is the current argument
   * we are processing, and pre stores the current arguments of
   *
   * For example, for a sygus grammar
   *   A -> and( A, A, B ) | true
   *   B -> false
   * passing arguments such that r=and( x1, x2, x3 ) to this function will add:
   *   and( x1, x2, x3 ) and and( x2, x1, x3 )
   * to terms.
   */
  std::unordered_set<Node> getGenericList(const SygusGrammar& g, const Node& r);
  /**
   * A recursive helper for the above method.
   * @param lam The lambda corresponding to the non-terminal rule (see
   * SygusGrammar::getLambdaForRule).
   * @param tset The set of terms we have computed thus far.
   * @param vlist The list of non-terminal variables and a unique index. The
   * variable we are considering for each p in this vector is
   * ntvMap[p.first][p.second].
   * @param ntlist The list of non-terminals (unique variables that occur
   * as the first component of some p in vlist).
   * @param ntvMap The partition of variables we are considering, grouped by
   * their corresponding non-terminal. We consider permutations of the
   * range of this map.
   * @param ntindex The non-terminal we are considering partitions for
   * @param vindex The sub-vector of variables for the current non-terminal
   * we are considering.
   */
  void getGenericListRec(const Node& lam,
                         std::unordered_set<Node>& tset,
                         const std::vector<std::pair<Node, size_t>>& vlist,
                         const std::vector<Node>& ntlist,
                         std::map<Node, std::vector<Node>>& ntvMap,
                         size_t ntindex,
                         size_t vindex);
  /** A set of intermediate variables introduced for the above method. */
  std::vector<Node> d_cacheValues;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYGUS_GRAMMAR_RED_H */

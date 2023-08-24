/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tianyi Liang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Strings Preprocess.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__PREPROCESS_H
#define CVC5__THEORY__STRINGS__PREPROCESS_H

#include <vector>

#include "context/cdhashmap.h"
#include "smt/env_obj.h"
#include "theory/rewriter.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/theory.h"
#include "util/hash.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** Strings preprocessor
 *
 * This class is responsible for extended function reductions. It is used as
 * a preprocessor when --no-strings-lazy-pp is enabled. By default, it is
 * used for reducing extended functions on-demand during the "extended function
 * reductions" inference schema of TheoryStrings.
 */
class StringsPreprocess : protected EnvObj
{
 public:
  StringsPreprocess(Env& env,
                    SkolemCache* sc,
                    HistogramStat<Kind>* statReductions = nullptr);
  ~StringsPreprocess();
  /** The reduce routine
   *
   * This is the main routine for constructing the reduction lemma for
   * an extended function t. It returns the simplified form of t, as well
   * as assertions for t, interpeted conjunctively.  The reduction lemma
   * for t is:
   *   asserts[0] ^ ... ^ asserts[n] ^ t = t'
   * where t' is the term returned by this method.
   * The argument sc defines the methods for generating new Skolem variables.
   * The return value is t itself if it is not reduced by this class.
   *
   * The reduction lemma for t is a way of specifying the complete semantics
   * of t. In other words, any model satisfying the reduction lemma of t
   * correctly interprets t.
   *
   * @param t The node to reduce,
   * @param asserts The vector for storing the assertions that correspond to
   * the reduction of t,
   * @param sc The skolem cache for generating new variables,
   * @param alphaCard The cardinality of the alphabet
   * @return The reduced form of t.
   */
  static Node reduce(Node t,
                     std::vector<Node>& asserts,
                     SkolemCache* sc,
                     size_t alphaCard);
  /**
   * Calls the above method for the skolem cache owned by this class, and
   * records statistics.
   */
  Node simplify(Node t, std::vector<Node>& asserts);
  /**
   * Applies simplifyRec on t until a fixed point is reached, and returns
   * the resulting term t', which is such that
   *   (exists k) asserts => t = t'
   * is valid, where k are the free skolems introduced when constructing
   * asserts.
   *
   * This method is called only for eager preprocessing of extended functions.
   */
  Node processAssertion(Node t, std::vector<Node>& asserts);

 private:
  /** pointer to the skolem cache used by this class */
  SkolemCache* d_sc;
  /** Reference to the statistics for the theory of strings/sequences. */
  HistogramStat<Kind>* d_statReductions;
  /** visited cache */
  std::map<Node, Node> d_visited;
  /**
   * Applies simplify to all top-level extended function subterms of t. New
   * assertions created in this reduction are added to asserts. The argument
   * visited stores a cache of previous results.
   *
   * This method is called only for eager preprocessing of extended functions.
   */
  Node simplifyRec(Node t, std::vector<Node>& asserts);
  /**
   * Makes the term returning the code point of string x at point i.
   */
  static Node mkCodePointAtIndex(Node x, Node i);
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__PREPROCESS_H */

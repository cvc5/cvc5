/*********************                                                        */
/*! \file theory_strings_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Strings Preprocess
 **
 ** Strings Preprocess.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__STRINGS__PREPROCESS_H
#define CVC4__THEORY__STRINGS__PREPROCESS_H

#include <vector>
#include "context/cdhashmap.h"
#include "theory/rewriter.h"
#include "theory/strings/sequences_stats.h"
#include "theory/strings/skolem_cache.h"
#include "theory/theory.h"
#include "util/hash.h"

namespace CVC4 {
namespace theory {
namespace strings {

/** Strings preprocessor
 *
 * This class is responsible for extended function reductions. It is used as
 * a preprocessor when --no-strings-lazy-pp is enabled. By default, it is
 * used for reducing extended functions on-demand during the "extended function
 * reductions" inference schema of TheoryStrings.
 */
class StringsPreprocess {
 public:
  StringsPreprocess(SkolemCache* sc,
                    context::UserContext* u,
                    SequencesStatistics& stats);
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
   * @return The reduced form of t.
   */
  static Node reduce(Node t, std::vector<Node>& asserts, SkolemCache* sc);
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
   */
  Node processAssertion(Node t, std::vector<Node>& asserts);
  /**
   * Replaces all formulas t in vec_node with an equivalent formula t' that
   * contains no free instances of extended functions (that is, extended
   * functions may only appear beneath quantifiers). This applies simplifyRec
   * on each assertion in vec_node until a fixed point is reached.
   */
  void processAssertions(std::vector<Node>& vec_node);

 private:
  /** pointer to the skolem cache used by this class */
  SkolemCache* d_sc;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /**
   * Applies simplify to all top-level extended function subterms of t. New
   * assertions created in this reduction are added to asserts. The argument
   * visited stores a cache of previous results.
   */
  Node simplifyRec(Node t,
                   std::vector<Node>& asserts,
                   std::map<Node, Node>& visited);
  /**
   * Make internal quantified formula with bound variable list bvl and body.
   * Internally, we get a node corresponding to marking a quantified formula as
   * an "internal" one. This node is provided as the third argument of the
   * FORALL returned by this method. This ensures that E-matching is not applied
   * to the quantified formula.
   */
  static Node mkForallInternal(Node bvl, Node body);
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__PREPROCESS_H */

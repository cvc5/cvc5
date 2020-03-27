/*********************                                                        */
/*! \file theory_strings_preprocess.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tianyi Liang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
  /**
   * Returns a node t' such that
   *   (exists k) new_nodes => t = t'
   * is valid, where k are the free skolems introduced when constructing
   * new_nodes.
   */
  Node simplify(Node t, std::vector<Node>& new_nodes);
  /**
   * Applies simplifyRec on t until a fixed point is reached, and returns
   * the resulting term t', which is such that
   *   (exists k) new_nodes => t = t'
   * is valid, where k are the free skolems introduced when constructing
   * new_nodes.
   */
  Node processAssertion(Node t, std::vector<Node>& new_nodes);
  /**
   * Replaces all formulas t in vec_node with an equivalent formula t' that
   * contains no free instances of extended functions (that is, extended
   * functions may only appear beneath quantifiers). This applies simplifyRec
   * on each assertion in vec_node until a fixed point is reached.
   */
  void processAssertions(std::vector<Node>& vec_node);

 private:
  /** commonly used constants */
  Node d_zero;
  Node d_one;
  Node d_neg_one;
  Node d_empty_str;
  /** pointer to the skolem cache used by this class */
  SkolemCache* d_sc;
  /** Reference to the statistics for the theory of strings/sequences. */
  SequencesStatistics& d_statistics;
  /**
   * Applies simplify to all top-level extended function subterms of t. New
   * assertions created in this reduction are added to new_nodes. The argument
   * visited stores a cache of previous results.
   */
  Node simplifyRec(Node t,
                   std::vector<Node>& new_nodes,
                   std::map<Node, Node>& visited);
};

}/* CVC4::theory::strings namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__STRINGS__PREPROCESS_H */

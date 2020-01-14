/*********************                                                        */
/*! \file example_cache.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief utility for processing programming by examples synthesis conjectures
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__EXAMPLE_CACHE_H
#define CVC4__THEORY__QUANTIFIERS__EXAMPLE_CACHE_H

#include "expr/node_trie.h"
#include "theory/evaluator.h"
#include "theory/quantifiers/sygus/example_infer.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * Example Cache
 *
 * This class is designed to evaluate a term on a set of substitutions
 * with a fixed domain.
 *
 * Its key feature is that substitutions that are identical over the free
 * variables of the term are not recomputed. For example, say I wish to evaluate
 * x+5 on substitutions having the domain { x, y }. Then, for the substitutions:
 *  { x -> 0, y -> 1 }
 *  { x -> 0, y -> 2 }
 *  { x -> 0, y -> 3 }
 *  { x -> 1, y -> 3 }
 * I would only compute the result of 0+5 once. On the other hand, evaluating
 * x+y for the above substitutions would require 4 evaluations.
 *
 * To use this class, call initialize(n,vars) first and then
 * evaluate(subs_1) ... evaluate(subs_n) as desired. Details on these methods
 * can be found below.
 */
class ExampleCache
{
 public:
  ExampleCache() {}
  ~ExampleCache();
  /** initialize this cache to evaluate n on substitutions with domain vars. */
  void initialize(Node n, const std::vector<Node>& vars);
  /**
   * Return the result of evaluating n * { vars -> subs } where vars is the
   * set of variables passed to initialize above.
   */
  Node evaluate(const std::vector<Node>& subs);

 private:
  /** The node to evaluate */
  Node d_evalNode;
  /** The domain of substitutions */
  std::vector<Node> d_vars;
  /** The indices in d_vars that occur free in n */
  std::vector<unsigned> d_indices;
  /**
   * The trie of results. This maps subs[d_indices[0]] .. subs[d_indices[j]]
   * to the result of the evaluation. For the example at the top of this class,
   * this trie would map (0) -> 5, (1) -> 6.
   */
  NodeTrie d_trie;
  /** The evaluator utility */
  Evaluator d_eval;
};

}  // namespace quantifiers
}  // namespace theory
} /* namespace CVC4 */

#endif

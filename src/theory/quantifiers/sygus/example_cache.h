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
 * This class is designed to 
 */
class ExampleCache
{
 public:
  ExampleCache() {}
  ~ExampleCache();
  /** initialize */
  void initialize(Node n, const std::vector< Node >& vars);
  /** evaluate */
  Node evaluate(const std::vector< Node >& subs);
 private:
  /** The node */
  Node d_evalNode;
  /** The variables */
  std::vector< Node > d_vars;
  /** The indices that are unique for n */
  std::vector< unsigned > d_indices;
  /** The trie of results */
  NodeTrie d_trie;
  /** The evaluator utility */
  Evaluator d_eval;
};

} /* namespace CVC4::theory::quantifiers */
} /* namespace CVC4::theory */
} /* namespace CVC4 */

#endif

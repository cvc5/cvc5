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
 * A class for mining interesting unsat queries from a stream of generated
 * expressions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUERY_GENERATOR_UNSAT_H
#define CVC5__THEORY__QUANTIFIERS__QUERY_GENERATOR_UNSAT_H

#include <map>
#include <unordered_set>

#include "expr/node.h"
#include "expr/variadic_trie.h"
#include "options/options.h"
#include "theory/quantifiers/lazy_trie.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * QueryGeneratorUnsat
 *
 * A module for generating interesting unsatisfiable benchmarks using SyGuS
 * enumeration. At a high level, this is based on conjoining predicates that
 * refine models and avoid previously encountered unsat cores.
 */
class QueryGeneratorUnsat : public QueryGenerator
{
 public:
  QueryGeneratorUnsat(Env& env);
  ~QueryGeneratorUnsat() {}
  /**
   * Add term to this module. This may trigger the printing and/or checking of
   * new queries.
   */
  bool addTerm(Node n, std::vector<Node>& queries) override;

 private:
  /**
   * Check current query, given by conjunction activeTerms. The generated
   * query is printed on out. If this is UNSAT, we add its unsat core to
   * d_cores. If it is satisfiable, we add its model to currModel for
   * its free variables (which are ExprMiner::d_skolems).
   */
  Result checkCurrent(const Node& qy,
                      std::vector<Node>& currModel,
                      std::vector<Node>& queries);
  /**
   * Get next random index, which returns a random index [0, d_terms.size()-1]
   * that is not already in processed.
   */
  size_t getNextRandomIndex(const std::unordered_set<size_t>& processed) const;
  /** Constant nodes */
  Node d_true;
  Node d_false;
  /** cache of all terms registered to this generator */
  std::vector<Node> d_terms;
  /** containing the unsat cores */
  VariadicTrie d_cores;
  /** The options for subsolver calls */
  Options d_subOptions;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS___H */

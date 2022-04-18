/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Wu
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PartitionGenerator for creating partitions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <vector>

#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/theory.h"
#include "theory/valuation.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {
class PropEngine;
}

namespace theory {

class PartitionGenerator : protected EnvObj
{
 public:
  PartitionGenerator(Env& env,
                     TheoryEngine* theoryEngine,
                     prop::PropEngine* propEngine);

  /**
   * Make partitions for parallel solving. e communicates the effort at which
   * check was called. Returns a lemma blocking off the emitted cube from the
   * search.
   */
  TrustNode check(Theory::Effort e);

 private:
  /**
   * Print the cube to the specified output.
   */
  void emitCube(Node toEmit);

  /**
   * Partition using the "revised" strategy, which emits cubes such as C1, C2,
   * C3, !C1 & !C2 & !C3
   */
  TrustNode makeRevisedPartitions();

  /**
   * Generate a lemma that is the negation of toBlock which ultimately blocks
   * that path in the search.
   */
  TrustNode blockPath(TNode toBlock);

  /**
   * Stop partitioning and return unsat.
   */
  TrustNode stopPartitioning() const;

  /**
   * Get the list of decisions from the SAT solver
   */
  std::vector<TNode> collectDecisionLiterals();

/**
 * Returns the d_cubes, the cubes that have been created for partitioning the
 * original problem.
 */
std::vector<Node> getPartitions() const { return d_cubes; }

/**
 * Current propEngine.
 */
prop::PropEngine* d_propEngine;

/**
 * Valuation of the theory engine.
 */
std::unique_ptr<Valuation> d_valuation;

/**
 * The number of partitions requested through the compute-partitions option.
 */
const uint64_t d_numPartitions;

/**
 * Number of standard or full (depending on partition check mode) checks that
 * have occured.
 */
uint64_t d_numChecks;

/**
 * The number of partitions that have been created.
 */
uint64_t d_numPartitionsSoFar;

/**
 * Lemmas that have been sent to the SAT solver.
 */
std::vector<Node> d_assertedLemmas;

/**
 * List of the cubes that have been created.
 */
std::vector<Node> d_cubes;

/**
 * Minimum number of literals required in the list of decisions for cubes to
 * be made.
 */
uint64_t d_conflictSize;
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */

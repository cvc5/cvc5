/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/theory.h"
#include "theory/theory_engine_module.h"
#include "theory/valuation.h"

namespace cvc5::internal {

namespace prop {
class PropEngine;
}

namespace theory {

class PartitionGenerator : public TheoryEngineModule
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
  void check(Theory::Effort e) override;

 private:
  /* LiteralListType is used to specify where to pull literals from when calling
   * collectLiterals. HEAP for the order_heap in the SAT solver, DECISION for
   * the decision trail in the SAT solver, and ZLL for the zero-level learned
   * literals.
   */
  enum LiteralListType
  {
    HEAP,
    DECISION,
    ZLL
  };
  /**
   * Increment d_numPartitionsSoFar and print the cube to 
   * the output file specified by --write-partitions-to. 
   */
  void emitCube(Node toEmit);

  /**
   * Partition using the "revised" strategy, which emits cubes such as C1, C2,
   * C3, !C1 & !C2 & !C3. If strict is set to true, a modified version of this
   * emits "strict cubes:" C1, !C1 & C2, !C1 & !C2 & C3, !C1 & !C2 & !C3. If
   * emitZLL is set to true, then zero-level learned literals will be appended
   * to the cubes.
   */
  Node makeRevisedPartitions(bool strict, bool emitZLL);

  /**
   * Partition by taking a list of literals and emitting mutually exclusive
   * cubes that resemble entries in a truth table: 
   * C1: { l1, !l2}
   * C2: { l1,  l2}
   * C3: {!l1, !l2}
   * C4: {!l1,  l2}
   * If emitZLL is set to true, then zero-level learned literals will be
   * appended to the cubes.
   */
  Node makeFullTrailPartitions(LiteralListType litType, bool emitZLL);

  /**
   * Generate a lemma that is the negation of toBlock which ultimately blocks
   * that path in the search.
   */
  Node blockPath(TNode toBlock);

  /**
   * Stop partitioning and return unsat.
   */
  Node stopPartitioning() const;

  /**
   * Get a list of literals.
   * litType specifies whether to pull from the decision trail in the sat solver,
   * from the order heap in the sat solver, or from the zero level learned literals.
   */
  std::vector<Node> collectLiterals(LiteralListType litType);

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
 * Number of standard checks that have occured since the last partition that was emitted. 
 */
uint64_t d_betweenChecks;

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
 * List of the strict cubes that have been created.
 */
std::vector<Node> d_strict_cubes;

/**
 * Minimum number of literals required in the list of decisions for cubes to
 * be made.
 */
uint64_t d_conflictSize;
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */

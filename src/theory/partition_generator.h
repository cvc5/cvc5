/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

#include <chrono>
#include <unordered_map>
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
   * postsolve, emits remaining partitions.
   */
  void postsolve(prop::SatValue result) override;

  /**
   * Make partitions for parallel solving. e communicates the effort at which
   * check was called. Returns a lemma blocking off the emitted cube from the
   * search.
   */
  void check(Theory::Effort e) override;

  /** Notify lemma, adds the literals from the Node n to our list of literals
   * from lemmas.
   */
  void notifyLemma(TNode n,
                   InferenceId id,
                   LemmaProperty p,
                   const std::vector<Node>& skAsserts,
                   const std::vector<Node>& sks) override;

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
    LEMMA,
    ZLL
  };
  /**
   * Increment d_numPartitionsSoFar and print the cube to 
   * the output file specified by --write-partitions-to. 
   */
  void emitPartition(Node toEmit);

  /**
   * Emit any remaining partitions that were not emitted during solving.
   */
  void emitRemainingPartitions(bool solved);

  /**
   * Helper for managing lemma atoms.
   */
  void incrementOrInsertLemmaAtom(Node& node);

  /**
   * Make scatter partitions: C1, !C1 & C2, !C1 & !C2 & C3, !C1 & !C2 & !C3.
   * litType: indicates the atom source.
   * emitZLL: if set to true, then zero-level learned literals will be appended
   * to the cubes.
   * timedOut: indicates timeout has occurred, so partitions must be dumped.
   * randomize: determines whether atoms are randomly chosen.
   */
  Node makeScatterPartitions(LiteralListType litType,
                             bool emitZLL,
                             bool timedOut,
                             bool randomize);

  /**
   * Partition by taking a list of literals and emitting mutually exclusive
   * cubes that resemble entries in a truth table:
   * C1: { l1, !l2}
   * C2: { l1,  l2}
   * C3: {!l1, !l2}
   * C4: {!l1,  l2}
   * litType: indicates the atom source.
   * emitZLL: if set to true, then zero-level learned literals will be appended
   * to the cubes.
   * randomize: determines whether atoms are randomly chosen.
   */
  Node makeCubePartitions(LiteralListType litType,
                          bool emitZLL,
                          bool randomize);

  /**
   * Generate a lemma that is the negation of toBlock which ultimately blocks
   * that path in the search.
   */
  Node blockPath(TNode toBlock);

  /**
   * Stop partitioning and return unsat.
   */
  Node stopPartitioning();

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
 * Check if we can use the atom represented by Node n.
 */
bool isUnusable(Node n);

/**
 * The time point when this partition generator was instantiated, used to
 * compute elapsed time.
 */
std::chrono::time_point<std::chrono::steady_clock> d_startTime;

/**
 * Used to track the inter-partition time.
 */
std::chrono::time_point<std::chrono::steady_clock>
    d_startTimeOfPreviousPartition;

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
 * List of the scatter partitions that have been created.
 */
std::vector<Node> d_scatterPartitions;

/**
 * Minimum number of literals required in the list of decisions for cubes to
 * be made.
 */
uint64_t d_conflictSize;

/**
 * Track whether any partitions have been emitted.
 */
bool d_createdAnyPartitions;

/**
 * Track whether all partitions have been emitted.
 */
bool d_emittedAllPartitions;

/**
 * Track lemma literals that we have seen and their frequency.
 */
std::unordered_map<Node, uint64_t> d_lemmaMap;

/**
 * Track lemma literals we have seen.
 */
std::set<Node> d_lemmaLiterals;

/**
 * Track lemma literals we have used in DNCs.
 */
std::set<Node> d_usedLemmaLiterals;
};
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__PARTITION__GENERATOR_H */

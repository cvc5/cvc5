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
 * Splitter for creating partitions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <fstream>
#include <sstream>
#include <vector>

#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/valuation.h"

namespace cvc5 {

class TheoryEngine;

namespace prop {
class PropEngine;
}

namespace theory {

class Splitter : protected EnvObj
{
 public:
  // Splitter
  Splitter(Env& env, TheoryEngine* theoryEngine, prop::PropEngine* propEngine);

  /**
   * Make partitions for parallel solving.
   */
  TrustNode makePartitions();

 private:
  /**
   * Print the cube to the specified output.
   */
  void emitCube(Node toEmit);

  /**
   * Block a path in the search by sending the not of toBlock as a lemma to the
   * SAT solver.
   */
  TrustNode blockPath(TNode toBlock);

  /**
   * Stop partitioning and return unsat.
   */
  TrustNode stopPartitioning();

  /**
   * Get the list of decisions from the SAT solver
   */
  void collectDecisionLiterals(std::vector<TNode>& literals);

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
   * The filestream for writing the partitions.
   */
  std::unique_ptr<std::ofstream> d_fileStream;

  /**
   * The output stream: either std::cout or the filestream if an output file is
   * specified.
   */
  std::ostream* d_output;

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
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */

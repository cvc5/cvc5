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
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SPLITTER_H
#define CVC5__THEORY__SPLITTER_H

#include <math.h>

#include <fstream>
#include <list>
#include <sstream>

#include "options/smt_options.h"
#include "proof/trust_node.h"
#include "theory/valuation.h"

namespace cvc5 {

class TheoryEngine;

namespace prop {
class PropEngine;
}

namespace theory {

class Splitter
{
 public:
  Splitter(TheoryEngine* theoryEngine, prop::PropEngine* propEngine);

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
  TrustNode blockPath(Node toBlock);

  /**
   * Close the output file if it is specified.
   */
  void closeFile();

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
  const unsigned d_numPartitions;

  /**
   * How long to wait in terms of the number of checks until creating the first
   * partition.
   */
  unsigned d_numChecks;

  /**
   * The number of partitions that have been created.
   */
  unsigned d_numPartitionsSoFar;

  /**
   * The name of the output file to write the partitions.
   */
  std::string d_partitionFile;

  /**
   * The filestream for writing the partitions.
   */
  std::ofstream d_partitionFileStream;

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
  unsigned d_conflictSize;
};
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */

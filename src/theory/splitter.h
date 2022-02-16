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
class ZeroLevelLearner;
}

namespace theory {

class Splitter
{
 public:
  Splitter(TheoryEngine* theoryEngine, prop::PropEngine* propEngine)
      : d_numPartitions(options::computePartitions()),
        d_numPartitionsSoFar(0),
        d_numChecks(0),
        d_partitionFile(options::writePartitionsToFileName())
  {
    // Assert(numPartitions > 1);
    d_valuation = std::make_unique<Valuation>(theoryEngine);
    d_propEngine = propEngine;
    d_output = &std::cout;
    if (d_partitionFile != "")
    {
      d_partitionFileStream.open(d_partitionFile);
      d_output = &d_partitionFileStream;
      d_partitionFileStream.close();
    }
  }

  TrustNode makePartitions();

 private:
  prop::PropEngine* d_propEngine;
  std::unique_ptr<Valuation> d_valuation;
  const unsigned d_numPartitions;
  unsigned d_numChecks;
  unsigned d_numPartitionsSoFar;
  std::string d_partitionFile;
  std::ofstream d_partitionFileStream;
  std::ostream* d_output;
  std::list<Node> d_assertedLemmas;
  std::vector<Node> d_cubes;
  TrustNode makeFinalConflict();
  void collectLiteralsOld(std::vector<TNode>& literals);
  void collectLiteralsNew(std::vector<TNode>& literals);
};
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__SPLITTER_H */

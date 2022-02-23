/*
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
 * The trust node utility.
 */

#include "theory/splitter.h"

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "prop/zero_level_learner.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

using namespace std;
using namespace cvc5::theory;

namespace cvc5 {

namespace theory {
Splitter::Splitter(TheoryEngine* theoryEngine, prop::PropEngine* propEngine)
    : d_numPartitions(options::computePartitions()),
      d_numChecks(0),
      d_numPartitionsSoFar(0),
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
  if (options::partitionConflictSize() == 0)
  {
    d_conflictSize = (unsigned)log2(d_numPartitions);
  }
  else
  {
    d_conflictSize = options::partitionConflictSize();
  }
}

void Splitter::collectDecisionLiterals(std::vector<TNode>& literals)
{
  std::vector<Node> decisionNodes = d_propEngine->getPropDecisions();
  for (Node n : decisionNodes)
  {
    Node originalN = SkolemManager::getOriginalForm(n);

    // Make sure the literal does not have a boolean term or skolem in it.
    std::unordered_set<Kind, kind::KindHashFunction> kinds = {
        kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE, kind::CONST_BOOLEAN};

    // If the literal is the not of some node, do the checks for the child
    // of the not instead of the not itself.
    Node original = originalN.getKind() == kind::NOT ? originalN[0] : originalN;
    if (expr::hasSubtermKinds(kinds, original)
        || !d_valuation->isSatLiteral(original)
        || !d_valuation->isDecision(original)
        || Theory::theoryOf(original) == THEORY_BOOL)
    {
      continue;
    }

    literals.push_back(originalN);
  }
}

void Splitter::emitCube(Node toEmit)
{
  *d_output << toEmit << "\n";
  ++d_numPartitionsSoFar;
}

void Splitter::closeFile()
{
  if (d_partitionFile != "")
  {
    d_partitionFileStream.close();
  }
}

TrustNode Splitter::blockPath(Node toBlock)
{
  // Now block the path in the search.
  Node lemma = toBlock.notNode();
  d_assertedLemmas.push_back(lemma);
  TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
  return trustedLemma;
}

// Send lemma that is the negation of all previously asserted lemmas.
TrustNode Splitter::stopPartitioning()
{
  Node lemma = NodeManager::currentNM()->mkAnd(d_assertedLemmas).notNode();
  return TrustNode::mkTrustLemma(lemma);
}

TrustNode Splitter::makePartitions()
{
  d_numChecks = d_numChecks + 1;

  if (d_numChecks < options::numChecks())
  {
    return TrustNode::null();
  }

  if (d_partitionFile != "")
  {
    d_partitionFileStream.open(d_partitionFile, std::ios_base::app);
    d_output = &d_partitionFileStream;
  }

  options::PartitionMode pmode = options::partitionStrategy();

  // This is the revised version of the old splitting strategy.
  // Cubes look like the following:
  // C1 = l1_{1} & .... & l1_{d_conflictSize}
  // C2 = l2_{1} & .... & l2_{d_conflictSize}
  // C3 = l3_{1} & .... & l3_{d_conflictSize}
  // C4 = !C1 & !C2 & !C3
  if (pmode == options::PartitionMode::REVISED)
  {
    // If we're not at the last cube
    if (d_numPartitionsSoFar < d_numPartitions - 1)
    {
      std::vector<TNode> literals;
      collectDecisionLiterals(literals);

      // Make sure we have enough literals.
      // Conflict size can be set through options, but the default is log base 2
      // of the requested number of partitions.
      if (literals.size() < d_conflictSize) return TrustNode::null();

      literals.resize(d_conflictSize);
      // Make first cube and emit it.
      Node conj = NodeManager::currentNM()->mkAnd(literals);
      emitCube(conj);
      // Add to the list of cubes. 
      d_cubes.push_back(conj);
      closeFile();
      return blockPath(conj);
    }

    // At the last cube
    else
    {
        vector<Node> nots;
        for (auto c : d_cubes) nots.push_back(c.notNode());
        Node lemma = NodeManager::currentNM()->mkAnd(nots);
        // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
        emitCube(lemma);
        closeFile();
        return stopPartitioning();
    }

    closeFile();
    return TrustNode::null();
  }

  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5

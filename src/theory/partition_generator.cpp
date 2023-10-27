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

#include "theory/partition_generator.h"

#include <math.h>

#include "expr/node_algorithm.h"
#include "expr/node_builder.h"
#include "options/parallel_options.h"
#include "prop/prop_engine.h"
#include "prop/theory_proxy.h"
#include "prop/zero_level_learner.h"
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"

using namespace std;

namespace cvc5::internal {

namespace theory {
PartitionGenerator::PartitionGenerator(Env& env,
                                       TheoryEngine* theoryEngine,
                                       prop::PropEngine* propEngine)
    : TheoryEngineModule(env, theoryEngine, "PartitionGenerator"),
      d_numPartitions(options().parallel.computePartitions),
      d_numChecks(0),
      d_betweenChecks(0),
      d_numPartitionsSoFar(0),
      d_createdAnyPartitions(false),
      d_emittedAllPartitions(false)
{
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

std::vector<Node> PartitionGenerator::collectLiterals(LiteralListType litType)
{
  std::vector<Node> filteredLiterals;
  std::vector<Node> unfilteredLiterals;

  switch (litType)
  {
    case DECISION:
    {
      unfilteredLiterals = d_propEngine->getPropDecisions();
      break;
    }
    case HEAP:
    { 
      unfilteredLiterals = d_propEngine->getPropOrderHeap(); 
      break;
    }
    case ZLL:
    {
      unfilteredLiterals = d_propEngine->getLearnedZeroLevelLiterals(
          modes::LearnedLitType::INPUT);
      break;
    }
    default: return filteredLiterals;
  }

  if (litType == HEAP || litType == DECISION)
  {
    for (const Node& n : unfilteredLiterals)
    {
      Node originalN = SkolemManager::getOriginalForm(n);
      modes::LearnedLitType nType = d_propEngine->getLiteralType(n);

      // If the literal is the not of some node, do the checks for the child
      // of the not instead of the not itself.
      Node original =
          originalN.getKind() == Kind::NOT ? originalN[0] : originalN;

      // Filter out the types of literals we don't want.
      // Make sure the literal does not have a skolem in it.
      if (expr::hasSubtermKind(Kind::SKOLEM, original)
          || !d_valuation->isSatLiteral(original)
          || Theory::theoryOf(original) == THEORY_BOOL || n.isConst()
          || nType != modes::LearnedLitType::INPUT
          || !d_valuation->isDecision(original))
      {
        continue;
      }
      filteredLiterals.push_back(originalN);
    }
  }
  // else it must be zll 
  else 
  {
    for (const Node& n : unfilteredLiterals)
    {
      Node originalN = SkolemManager::getOriginalForm(n);

      // If the literal is the not of some node, do the checks for the child
      // of the not instead of the not itself.
      Node original =
          originalN.getKind() == Kind::NOT ? originalN[0] : originalN;

      if (expr::hasSubtermKind(Kind::SKOLEM, original)
          || !d_valuation->isSatLiteral(original)
          || Theory::theoryOf(original) == THEORY_BOOL || n.isConst())
      {
        continue;
      }
      filteredLiterals.push_back(originalN);
    }
  }
  
  return filteredLiterals;
}

void PartitionGenerator::emitPartition(Node toEmit)
{
  *options().parallel.partitionsOut << toEmit << std::endl;
  ++d_numPartitionsSoFar;
  d_createdAnyPartitions = true;
}

Node PartitionGenerator::blockPath(TNode toBlock)
{
  // Now block the path in the search.
  Node lemma = toBlock.notNode();
  d_assertedLemmas.push_back(lemma);
  return lemma;
}

// Send lemma that is the negation of all previously asserted lemmas.
Node PartitionGenerator::stopPartitioning()
{
  d_emittedAllPartitions = true;
  return NodeManager::currentNM()->mkConst(false);
}

// This is the revised version of the old splitting strategy.
// Cubes look like the following:
// C1 = l1_{1} & .... & l1_{d_conflictSize}
// C2 = l2_{1} & .... & l2_{d_conflictSize}
// C3 = l3_{1} & .... & l3_{d_conflictSize}
// C4 = !C1 & !C2 & !C3
Node PartitionGenerator::makeRevisedPartitions(bool emitZLL)
{
  // If we're not at the last cube
  if (d_numPartitionsSoFar < d_numPartitions - 1)
  {
    std::vector<Node> literals = collectLiterals(DECISION);

    // Make sure we have enough literals.
    // Conflict size can be set through options, but the default is log base 2
    // of the requested number of partitions.
    if (literals.size() < d_conflictSize)
    {
      return Node::null();
    }

    literals.resize(d_conflictSize);

    // Make a cube from the literals
    Node conj = NodeManager::currentNM()->mkAnd(literals);

    // Add the conjunction to the list of cubes.
    d_cubes.push_back(conj);

    // For the scatter strategy, partitions look like the following:
    // P1 =              C1 = l1_{1} & .... & l1_{d_conflictSize}
    // P2 = !C1 &        C2 = l2_{1} & .... & l2_{d_conflictSize}
    // P3 = !C1 & !C2 &  C3 = l3_{1} & .... & l3_{d_conflictSize}
    // P4 = !C1 & !C2 & !C3
    vector<Node> toEmit;

    // Collect negation of the previously used cubes.
    for (const Node& c : d_cubes)
    {
      toEmit.push_back(c.notNode());
    }

    // Add the current cube.
    toEmit.push_back(conj);

    // Now make the scatter partition and add it to the list of partitions.
    Node scatterPartition = NodeManager::currentNM()->mkAnd(toEmit);
    d_scatterPartitions.push_back(scatterPartition);

    // Just increment and don't actually output the partition yet
    d_numPartitionsSoFar++;

    // Track that we have created at least one partition
    d_createdAnyPartitions = true;

    return blockPath(conj);
  }

  // Otherwise, we are at the last partition, and we should emit all partitions
  // now.
  emitRemainingPartitions(/*solved=*/false);
  return stopPartitioning();
}

Node PartitionGenerator::makeFullTrailPartitions(LiteralListType litType,
                                                 bool emitZLL)
{
  std::vector<Node> literals = collectLiterals(litType);
  uint64_t numVar = static_cast<uint64_t>(log2(d_numPartitions));
  if (literals.size() >= numVar)
  {
    literals.resize(numVar);

    // This complicated thing is basically making a truth table
    // of with 2^numVar variable so that each row can be emitted as a partition
    // later. Each entry in resultNodeLists is a row corresponding to a cube:
    // resultNodeLists = {
    //   { l1,  l2}
    //   { l1, !l2}
    //   {!l1,  l2}
    //   {!l1, !l2} }

    // total number of cubes/rows
    size_t total = pow(2, numVar);

    // resultNodeLists is built column by column. 
    std::vector<std::vector<Node> > resultNodeLists(total);

    // t is used to determine whether to push the node or its not_node.
    bool t = false;

    // numConsecutiveTF tracks how many times the node should be consectuively 
    // true or false in a column.
    // For example, if numVar=3:
    // x y z
    // T T T
    // T T F
    // T F T
    // T F F
    // F T T
    // F T F
    // F F T
    // F F F
    // For the first column, numConsecutiveTF = 4, then 2 for the second column, 
    // and 1 for the third column.
    size_t numConsecutiveTF = total / 2;
    for (Node n : literals)
    {
      Node not_n = n.notNode();

      // loc tracks which row/cube we're on 
      size_t loc = 0;
      for (size_t z = 0; z < total / numConsecutiveTF; ++z)
      {
        t = !t;
        for (size_t j = 0; j < numConsecutiveTF; ++j)
        {
          resultNodeLists[loc].push_back(t ? n : not_n);
          ++loc;
        }
      }

      numConsecutiveTF = numConsecutiveTF / 2;
    }
    for (const std::vector<Node>& row : resultNodeLists)
    {
      Node conj = NodeManager::currentNM()->mkAnd(row);
      if (emitZLL)
      {
        std::vector<Node> zllLiterals = collectLiterals(ZLL);
        zllLiterals.push_back(conj);
        Node zllConj = NodeManager::currentNM()->mkAnd(zllLiterals);
        emitPartition(zllConj);
      }
      else {
        emitPartition(conj);
      } 
    }
    return stopPartitioning();
  }
  return Node::null();
}

void PartitionGenerator::emitRemainingPartitions(bool solved)
{
  if (d_emittedAllPartitions)
  {
    return;
  }

  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  std::vector<Node> zllLiterals;

  if (emitZLL)
  {
    zllLiterals =
        d_propEngine->getLearnedZeroLevelLiterals(modes::LearnedLitType::INPUT);
  }

  for (const auto& partition : d_scatterPartitions)
  {
    Node lemma = partition;

    if (emitZLL)
    {
      zllLiterals.push_back(partition);
      lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
      zllLiterals.pop_back();
    }

    emitPartition(lemma);
  }

  // If the problem has been solved, then there is no need to emit
  // the final partition because it was solved by the partitioning solver.
  // However, if the problem has not been solved by this solver, then
  // we must emit the final partition.
  if (!solved)
  {
    std::vector<Node> nots;
    for (const Node& cube : d_cubes)
    {
      nots.push_back(cube.notNode());
    }

    Node finalPartition = NodeManager::currentNM()->mkAnd(nots);

    if (emitZLL)
    {
      zllLiterals.push_back(finalPartition);
      finalPartition = NodeManager::currentNM()->mkAnd(zllLiterals);
    }

    emitPartition(finalPartition);
  }
}

void PartitionGenerator::check(Theory::Effort e)
{
  if ((options().parallel.partitionCheck == options::CheckMode::FULL
       && !Theory::fullEffort(e))
      || (options().parallel.partitionCheck == options::CheckMode::STANDARD
          && Theory::fullEffort(e))
      || (options().parallel.computePartitions < 2))
  {
    return;
  }

  d_numChecks = d_numChecks + 1;
  d_betweenChecks = d_betweenChecks + 1;

  if (d_numChecks < options().parallel.checksBeforePartitioning || 
      d_betweenChecks < options().parallel.checksBetweenPartitions)
  {
    return;
  }

  // Reset betweenChecks
  d_betweenChecks = 0;

  Node lem;
  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::HEAP_TRAIL:
      lem = makeFullTrailPartitions(/*litType=*/HEAP, emitZLL);
      break;
    case options::PartitionMode::DECISION_TRAIL:
      lem = makeFullTrailPartitions(/*litType=*/DECISION, emitZLL);
      break;
    case options::PartitionMode::DECISION_SCATTER:
      lem = makeRevisedPartitions(emitZLL);
      break;
    default: return;
  }
  // send the lemma if it exists
  if (!lem.isNull())
  {
    d_out.lemma(lem, InferenceId::PARTITION_GENERATOR_PARTITION);
  }
}

void PartitionGenerator::postsolve(prop::SatValue result)
{
  // Handle emitting pending partitions.
  // This can be triggered by a scatter strategy that produces
  // fewer than the requested number of partitions before solving
  // the remainder of the problem.
  if (result != prop::SatValue::SAT_VALUE_TRUE)
  {
    emitRemainingPartitions(/*solved=*/true);
  }
}

}  // namespace theory
}  // namespace cvc5::internal

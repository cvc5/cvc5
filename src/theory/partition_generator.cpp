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
      d_numPartitionsSoFar(0)
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
      unfilteredLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
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
      Node original = originalN.getKind() == kind::NOT ? originalN[0] : originalN;

      // Filter out the types of literals we don't want.
      // Make sure the literal does not have a skolem in it.
      if (expr::hasSubtermKind(kind::SKOLEM, original)
          || !d_valuation->isSatLiteral(original)
          || Theory::theoryOf(original) == THEORY_BOOL || n.isConst()
          || nType != modes::LEARNED_LIT_INPUT
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
      Node original = originalN.getKind() == kind::NOT ? originalN[0] : originalN;

      if (expr::hasSubtermKind(kind::SKOLEM, original)
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

void PartitionGenerator::emitCube(Node toEmit)
{
  *options().parallel.partitionsOut << toEmit << std::endl;
  ++d_numPartitionsSoFar;
}

Node PartitionGenerator::blockPath(TNode toBlock)
{
  // Now block the path in the search.
  Node lemma = toBlock.notNode();
  d_assertedLemmas.push_back(lemma);
  return lemma;
}

// Send lemma that is the negation of all previously asserted lemmas.
Node PartitionGenerator::stopPartitioning() const
{
  return NodeManager::currentNM()->mkConst(false);
}

// This is the revised version of the old splitting strategy.
// Cubes look like the following:
// C1 = l1_{1} & .... & l1_{d_conflictSize}
// C2 = l2_{1} & .... & l2_{d_conflictSize}
// C3 = l3_{1} & .... & l3_{d_conflictSize}
// C4 = !C1 & !C2 & !C3
Node PartitionGenerator::makeRevisedPartitions(bool strict, bool emitZLL)
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
    // Make cube from literals
    Node conj = NodeManager::currentNM()->mkAnd(literals);

    // For the strict-cube strategy, cubes look like the following:
    // C1 =             l1_{1} & .... & l1_{d_conflictSize}
    // C2 = !C1 &       l2_{1} & .... & l2_{d_conflictSize}
    // C3 = !C1 & !C2 & l3_{1} & .... & l3_{d_conflictSize}
    // C4 = !C1 & !C2 & !C3
    if (strict)
    {
      vector<Node> toEmit;
      for (const Node& c : d_cubes) 
      {
        toEmit.push_back(c.notNode());
      }
      toEmit.push_back(conj);
      Node strict_cube = NodeManager::currentNM()->mkAnd(toEmit);
      d_strict_cubes.push_back(strict_cube);

      if (emitZLL)
      {
        // just increment and don't actually output the cube yet
        d_numPartitionsSoFar++;
      }
      else 
      {
        emitCube(strict_cube);
      }
    }
    else {
      if (emitZLL)
      {
        // just increment and don't actually output the cube yet
        d_numPartitionsSoFar++;
      }
      else 
      {
        emitCube(conj);
      }
    }
    // Add to the list of cubes.
    d_cubes.push_back(conj);
    return blockPath(conj);
  }
  // At the last cube
  else
  {
    if (emitZLL) 
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      std::vector<Node>* cubes = strict ? &d_strict_cubes : &d_cubes;
      
      for (const auto& c : *cubes)
      {
        zllLiterals.push_back(c);
        Node lemma = NodeManager::currentNM()->mkAnd(zllLiterals);
        emitCube(lemma);
        zllLiterals.pop_back();
      }
    }

    vector<Node> nots;
    for (const Node& c : d_cubes)
    {
      nots.push_back(c.notNode());
    }
    Node lemma = NodeManager::currentNM()->mkAnd(nots);
    // Emit not(cube_one) and not(cube_two) and ... and not(cube_n-1)
    if (emitZLL) 
    {
      std::vector<Node> zllLiterals =
          d_propEngine->getLearnedZeroLevelLiterals(modes::LEARNED_LIT_INPUT);
      zllLiterals.push_back(lemma);
      Node zllLemma = NodeManager::currentNM()->mkAnd(zllLiterals);
      emitCube(zllLemma);
    }
    else {
      emitCube(lemma);
    }
    return stopPartitioning();
  }
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
        emitCube(zllConj);
      }
      else {
        emitCube(conj);
      } 
    }
    return stopPartitioning();
  }
  return Node::null();
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
    case options::PartitionMode::STRICT_CUBE:
      lem = makeRevisedPartitions(/*strict=*/true, emitZLL);
      break;
    case options::PartitionMode::REVISED:
      lem = makeRevisedPartitions(/*strict=*/false, emitZLL);
      break;
    default: return;
  }
  // send the lemma if it exists
  if (!lem.isNull())
  {
    d_out.lemma(lem);
  }
}

}  // namespace theory
}  // namespace cvc5::internal

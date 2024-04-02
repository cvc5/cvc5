/******************************************************************************
 * Top contributors (to current version):
 *   Amalee Wilson, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * PartitionGenerator for creating partitions.
 */

#include "theory/partition_generator.h"

#include <math.h>

#include <algorithm>
#include <random>

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
  d_startTime = std::chrono::steady_clock::now();
  d_startTimeOfPreviousPartition = std::chrono::steady_clock::now();
  d_valuation = std::make_unique<Valuation>(theoryEngine);
  d_propEngine = propEngine;

  d_conflictSize = options().parallel.partitionConflictSize;
  if (!d_conflictSize)
  {
    d_conflictSize = static_cast<uint64_t>(log2(d_numPartitions));
  }
}

void PartitionGenerator::incrementOrInsertLemmaAtom(Node& node)
{
  if (d_lemmaMap.count(node) == 0)
  {
    d_lemmaMap.insert({node, 1});
    d_lemmaLiterals.insert(node);
  }
  else
  {
    int new_count = d_lemmaMap[node] + 1;
    d_lemmaMap.erase(node);
    d_lemmaMap.insert({node, new_count});
  }
}

void PartitionGenerator::notifyLemma(TNode n,
                                     InferenceId id,
                                     LemmaProperty p,
                                     const std::vector<Node>& skAsserts,
                                     const std::vector<Node>& sks)
{
  if (options().parallel.partitionStrategy == options::PartitionMode::LEMMA_CUBE
      || options().parallel.partitionStrategy
             == options::PartitionMode::LEMMA_SCATTER)
  {
    std::vector<Node> toVisit;
    toVisit.push_back(n);

    for (unsigned i = 0; i < toVisit.size(); ++i)
    {
      Node current = toVisit[i];
      // If current node is theory bool, visit the children.
      if (Theory::theoryOf(current) == THEORY_BOOL)
      {
        for (unsigned child = 0, childEnd = current.getNumChildren();
             child < childEnd;
             ++child)
        {
          auto childNode = current[child];
          // If we haven't seen the child, we should visit it.
          if (d_lemmaMap.count(childNode) == 0)
          {
            toVisit.push_back(childNode);
          }
          else
          {
            // If we have already seen this chld node, then it is not theory
            // bool, so we update its entry. No need to visit again.
            incrementOrInsertLemmaAtom(childNode);
          }
        }
      }
      else
      {
        incrementOrInsertLemmaAtom(current);
      }
    }
  }
}

// Some of this function may be redundant, but I was trying to be
// complete.
bool PartitionGenerator::isUnusable(Node n)
{
  const std::unordered_set<Kind, kind::KindHashFunction> unusableKinds = {
      Kind::INST_CONSTANT, Kind::SKOLEM};

  // Check if n is constant or contains unusable kinds.
  if (n.isConst())
  {
    return true;
  }

  // Check if original has unusable kinds or contains skolems.
  Node originalN = SkolemManager::getOriginalForm(n);
  if (expr::hasSubtermKinds(unusableKinds, originalN))
  {
    return true;
  }

  // Get non negated versions before testing for bool expr.
  Node nonNegatedOriginal =
      originalN.getKind() == Kind::NOT ? originalN[0] : originalN;

  // Check if this is a boolean expression
  if (Theory::theoryOf(nonNegatedOriginal) == THEORY_BOOL)
  {
    return true;
  }

  return false;
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
    case LEMMA:
    {
      std::vector<Node> lemmaNodes(d_lemmaLiterals.size());
      std::copy(
          d_lemmaLiterals.begin(), d_lemmaLiterals.end(), lemmaNodes.begin());
      unfilteredLiterals = lemmaNodes;
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

  if (litType == LEMMA)
  {
    // Sort by frequency of the literal.
    std::sort(unfilteredLiterals.begin(),
              unfilteredLiterals.end(),
              [this](Node a, Node b) -> bool {
                return d_lemmaMap[a] > d_lemmaMap[b];
              });
  }

  // These checks may be unnecessary for ZLL.
  for (const Node& n : unfilteredLiterals)
  {
    if (isUnusable(n)
        || (litType == LEMMA && d_usedLemmaLiterals.count(n) != 0))
    {
      continue;
    }
    filteredLiterals.push_back(SkolemManager::getOriginalForm(n));
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
  return nodeManager()->mkConst(false);
}

// For the scatter strategy, we make the following kinds of partitions:
// P1 =              C1 = l1_{1} & ... & l1_{d_conflictSize}
// P2 = !C1 &        C2 = l2_{1} & ... & l2_{d_conflictSize}
// P3 = !C1 & !C2 &  C3 = l3_{1} & ... & l3_{d_conflictSize}
// P4 = !C1 & !C2 & !C3
// Note that we want to simply collect the partitions until we get to the
// timeout or total number of requested partitions.
// Once we reach that point, we dump all the partitions.
Node PartitionGenerator::makeScatterPartitions(LiteralListType litType,
                                               bool emitZLL,
                                               bool timedOut,
                                               bool randomize)
{
  // If we're not at the last cube
  if (d_numPartitionsSoFar < d_numPartitions - 1)
  {
    std::vector<Node> literals = collectLiterals(litType);

    // Make sure we have enough literals.
    // Conflict size can be set through options, but the default is log base
    // 2 of the requested number of partitions.
    if (literals.size() < d_conflictSize)
    {
      return Node::null();
    }

    if (randomize)
    {
      std::shuffle(literals.begin(),
                   literals.end(),
                   std::mt19937(std::random_device()()));
    }

    literals.resize(d_conflictSize);

    // Add literals to the seen list if we are using lemmas
    if (litType == LEMMA)
    {
      for (auto l : literals)
      {
        d_usedLemmaLiterals.insert(l);
      }
    }

    // Make a cube from the literals
    Node conj = nodeManager()->mkAnd(literals);

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

    // Add the conjunction to the list of cubesThis needs to happen after
    // collecting the negations of the previously used cubes.
    d_cubes.push_back(conj);

    // Add the current cube.
    toEmit.push_back(conj);

    // Now make the scatter partition and add it to the list of partitions.
    Node scatterPartition = nodeManager()->mkAnd(toEmit);
    d_scatterPartitions.push_back(scatterPartition);

    // Just increment and don't actually output the partition yet
    d_numPartitionsSoFar++;

    // Track that we have created at least one partition
    d_createdAnyPartitions = true;

    if (timedOut)
    {
      emitRemainingPartitions(/*solved=*/false);
      return stopPartitioning();
    }

    return blockPath(conj);
  }

  // Otherwise, we are at the last partition, and we should emit all
  // partitions now.
  emitRemainingPartitions(/*solved=*/false);
  return stopPartitioning();
}

Node PartitionGenerator::makeCubePartitions(LiteralListType litType,
                                            bool emitZLL,
                                            bool randomize)
{
  std::vector<Node> literals = collectLiterals(litType);
  uint64_t numVar = static_cast<uint64_t>(log2(d_numPartitions));
  if (literals.size() >= numVar)
  {
    if (randomize)
    {
      std::shuffle(literals.begin(),
                   literals.end(),
                   std::mt19937(std::random_device()()));
    }
    literals.resize(numVar);

    // This complicated thing is basically making a truth table
    // of with 2^numVar variable so that each row can be emitted as a
    // partition later. Each entry in resultNodeLists is a row corresponding
    // to a cube: resultNodeLists = {
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

    // numConsecutiveTF tracks how many times the node should be
    // consectuively true or false in a column.
    // clang-format off
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
    // clang-format on
    // For the first column, numConsecutiveTF = 4, then 2 for the
    //  second column, and 1 for the third column.
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
      Node conj = nodeManager()->mkAnd(row);
      if (emitZLL)
      {
        std::vector<Node> zllLiterals = collectLiterals(ZLL);
        zllLiterals.push_back(conj);
        Node zllConj = nodeManager()->mkAnd(zllLiterals);
        emitPartition(zllConj);
      }
      else
      {
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
      lemma = nodeManager()->mkAnd(zllLiterals);
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

    Node finalPartition = nodeManager()->mkAnd(nots);

    if (emitZLL)
    {
      zllLiterals.push_back(finalPartition);
      finalPartition = nodeManager()->mkAnd(zllLiterals);
    }

    emitPartition(finalPartition);
  }
}

void PartitionGenerator::check(Theory::Effort e)
{
  if ((options().parallel.partitionCheck == options::CheckMode::FULL
       && !Theory::fullEffort(e))
      || (options().parallel.computePartitions < 2))
  {
    return;
  }

  // This timing handles when the partitionTimeLimit is set. By default, it is
  // set to 60 seconds. The partitionTimeLimit is used to force the partition
  // generator to finish within a certain number of seconds.
  auto now = std::chrono::steady_clock::now();
  std::chrono::duration<double> totalElapsedTime = now - d_startTime;
  bool timeOutExceeded =
      totalElapsedTime.count() >= options().parallel.partitionTimeLimit;

  // This timing code handles the partition timing when the partition-when flag
  // is used to specify that, for example, the first partition should be made
  // after 3 seconds (partition-start-time=3) while the subsequent partitions
  // should be made at 1 second intervals (partition-time-interval=1.0).
  if (options().parallel.partitionWhen == options::PartitionWhenMode::TLIMIT)
  {
    std::chrono::duration<double> interElapsedTime =
        now - d_startTimeOfPreviousPartition;
    bool startTimeExceeded =
        totalElapsedTime.count() >= options().parallel.partitionStartTime;
    bool interTimeExceeded =
        interElapsedTime.count() >= options().parallel.partitionTimeInterval;

    // When using time limits, we partition if the partition start time is
    // exceeded and no partitions have been made, or when at least one partition
    // has been created and the inter-partition time limit has been exceeded
    bool timeLimitExceeded =
        ((d_createdAnyPartitions && interTimeExceeded)
         || (!d_createdAnyPartitions && startTimeExceeded));

    if (!timeLimitExceeded)
    {
      return;
    }
    // Reset start time of previous partition
    d_startTimeOfPreviousPartition = std::chrono::steady_clock::now();
  }
  else
  {
    d_numChecks = d_numChecks + 1;
    d_betweenChecks = d_betweenChecks + 1;

    bool checkLimitExceeded =
        ((d_createdAnyPartitions
          && d_betweenChecks >= options().parallel.checksBetweenPartitions)
         || (!d_createdAnyPartitions
             && d_numChecks >= options().parallel.checksBeforePartitioning));
    if (!checkLimitExceeded)
    {
      return;
    }
    // Reset betweenChecks
    d_betweenChecks = 0;
  }

  Node lem;
  bool emitZLL = options().parallel.appendLearnedLiteralsToCubes;
  bool randomize = options().parallel.randomPartitioning;
  switch (options().parallel.partitionStrategy)
  {
    case options::PartitionMode::HEAP_CUBE:
      lem = makeCubePartitions(/*litType=*/HEAP, emitZLL, randomize);
      break;
    case options::PartitionMode::DECISION_CUBE:
      lem = makeCubePartitions(/*litType=*/DECISION, emitZLL, randomize);
      break;
    case options::PartitionMode::LEMMA_CUBE:
      lem = makeCubePartitions(/*litType=*/LEMMA, emitZLL, randomize);
      break;
    case options::PartitionMode::HEAP_SCATTER:
      lem = makeScatterPartitions(
          /*litType=*/HEAP, emitZLL, timeOutExceeded, randomize);
      break;
    case options::PartitionMode::DECISION_SCATTER:
      lem = makeScatterPartitions(
          /*litType=*/DECISION, emitZLL, timeOutExceeded, randomize);
      break;
    case options::PartitionMode::LEMMA_SCATTER:
      lem = makeScatterPartitions(
          /*litType=*/LEMMA, emitZLL, timeOutExceeded, randomize);
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

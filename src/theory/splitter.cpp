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
#include "theory/theory_engine.h"
#include "theory/theory_id.h"
#include "theory/theory_traits.h"
#include "prop/zero_level_learner.h"
#include "prop/theory_proxy.h"

using namespace std;
using namespace cvc5::theory;

namespace cvc5 {

namespace theory {

void Splitter::collectDecisionLiterals(std::vector<TNode>& literals)
{

  std::vector<Node> decisionNodes = d_propEngine->getPropDecisions();
  for (Node n : decisionNodes)
  {
    Node originalN = SkolemManager::getOriginalForm(n);

    // Make sure the literal does not have a boolean term or skolem in it.
    std::unordered_set<Kind, kind::KindHashFunction> kinds = {
        kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};

    // If the literal is the not of some node, do the checks for the child
    // of the not instead of the not itself. 
    if (originalN.getKind() == kind::NOT) {
      if (expr::hasSubtermKinds(kinds, originalN[0]) ||
      !d_valuation->isSatLiteral(originalN[0]) || !d_valuation->isDecision(originalN[0])){
        continue;
      }
    } else if (expr::hasSubtermKinds(kinds, originalN) || !d_valuation->isSatLiteral(originalN)
        || !d_valuation->isDecision(originalN))
    {
      continue;
    }

    literals.push_back(originalN);
  }
}

TrustNode Splitter::makePartitions()
{
  d_numChecks = d_numChecks + 1;
  if (d_partitionFile != "")
  {
    d_partitionFileStream.open(d_partitionFile, std::ios_base::app);
    d_output = &d_partitionFileStream;
  }

  // This is the revised version of the old splitting strategy. 
  // Cubes look like the following: 
  // C1 = l1_{1} & .... & l1_{d_conflictSize}
  // C2 = l2_{1} & .... & l2_{d_conflictSize}
  // C3 = l3_{1} & .... & l3_{d_conflictSize}
  // C4 = !C1 & !C2 & !C3
  if (options::partitionStrategy() == "revised")
  {
    // If we're at the last cube
    if (d_numPartitionsSoFar == d_numPartitions - 1)
    {
      if (d_numPartitionsSoFar == 1)
      {
        *d_output << d_assertedLemmas.front() << "\n";
        NodeBuilder notBuilder(kind::NOT);
        notBuilder << d_assertedLemmas.front();
        Node lemma = notBuilder.constructNode();
        return TrustNode::mkTrustLemma(lemma);
      }
      // If we ask for more than two partitions.
      else
      {
        NodeBuilder andBuilder(kind::AND);
        for (const auto d : d_assertedLemmas)
        {
          NodeBuilder notBuilder(kind::NOT);
          notBuilder << d;
          Node negated_cube = notBuilder.constructNode();
          andBuilder << negated_cube;
        }

        Node last_cube = andBuilder.constructNode();
        *d_output << last_cube << "\n";

        if (d_partitionFile != "")
        {
          d_partitionFileStream.close();
        }

        NodeBuilder andBuilder2(kind::AND);
        for (const auto d : d_assertedLemmas) andBuilder2 << d;
        Node conj = andBuilder2.constructNode();
        NodeBuilder notBuilder(kind::NOT);
        notBuilder << conj;
        Node lemma = notBuilder.constructNode();
        ++d_numPartitionsSoFar;

        return TrustNode::mkTrustLemma(lemma);
      }
    }

    // Not at the last cube
    else
    {
      std::vector<TNode> literals;
      collectDecisionLiterals(literals);

      if (literals.size() >= d_conflictSize)
      {
        std::vector<Node> tmpLiterals(literals.begin(),
                                      literals.begin() + d_conflictSize);
        Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
        *d_output << conj << "\n";
        if (d_partitionFile != "")
        {
          d_partitionFileStream.close();
        }

        NodeBuilder notBuilder(kind::NOT);
        notBuilder << conj;
        Node lemma = notBuilder.constructNode();

        ++d_numPartitionsSoFar;
        d_assertedLemmas.push_back(lemma);

        TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
        return trustedLemma;
      }
    }
    if (d_partitionFile != "")
    {
      d_partitionFileStream.close();
    }

    return TrustNode::null();
  }

  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5

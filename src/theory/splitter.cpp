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

#include <math.h>

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

// TODO: determine whether the old or new way of collecting literals is better.
void Splitter::collectLiteralsOld(std::vector<TNode>& literals)
{
  // If you use only one theory, the list is (most likely) guaranteed to be in
  // order.
  for (TheoryId theoryId = THEORY_FIRST; theoryId < THEORY_LAST; ++theoryId)
  {
    for (context::CDList<Assertion>::const_iterator
             it = d_valuation->factsBegin(theoryId),
             it_end = d_valuation->factsEnd(theoryId);
         it != it_end;
         ++it)
    {
      TNode a = (*it).d_assertion;
      Node og = SkolemManager::getOriginalForm(a);

      // Is isSatLiteral ever false here???
      // Maybe just add an interface to access the decision trail in the sat
      // solver? This is kludgy Might be enough to check if decision.
      if (d_valuation->isSatLiteral(a) && d_valuation->isDecision(a))
      {
        // have a mapping of nodes to whether they qualify for the list.
        std::unordered_set<Kind, kind::KindHashFunction> kinds = {
            kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};
        if (expr::hasSubtermKinds(kinds, og)) continue;
        literals.push_back(og);
      }
    }
  }
}

// TODO: determine whether the old or new way of collecting literals is better.
void Splitter::collectLiteralsNew(std::vector<TNode>& literals)
{
  unsigned conflictSize = (unsigned)log2(d_numPartitions);

  std::vector<Node> decisionNodes = d_propEngine->getPropDecisions();
  for (Node n : decisionNodes)
  {
    TNode t = n;

    Node og = SkolemManager::getOriginalForm(n);

    // Make sure the literal does not have a boolean term in it
    // because partitions containing those would just look like fresh variables.
    std::unordered_set<Kind, kind::KindHashFunction> kinds = {
        kind::SKOLEM, kind::BOOLEAN_TERM_VARIABLE};

    if (expr::hasSubtermKinds(kinds, og) || !d_valuation->isSatLiteral(og)
        || !d_valuation->isDecision(og))
    {
      continue;
    }

    // This probably makes the new version produce the same cubes as old version
    // if (og.getKind() == kind::NOT) {
    //   if (expr::hasSubtermKinds(kinds, og[0]) ||
    //   !d_valuation->isSatLiteral(og[0]) || !d_valuation->isDecision(og[0])){
    //     continue;
    //   }
    // }

    literals.push_back(og);
  }
}

// TODO: if we get too many, just write the previous level
// if too fine grained, output the most fine grained still
// in your threshold.
TrustNode Splitter::makePartitions()
{
  d_numChecks = d_numChecks + 1;
  if (d_partitionFile != "")
  {
    d_partitionFileStream.open(d_partitionFile, std::ios_base::app);
    d_output = &d_partitionFileStream;
  }

  // The strict cube strategy makes cubes like this:
  //  c1 
  // !c1 &  c2
  // !c1 & !c2 &  c3
  // !c1 & !c2 & !c3
  if (options::partitionStrategy() == "strict-cube")
  {
    // If we're at the last cube
    if (d_numPartitionsSoFar == d_numPartitions - 1)
    {
      // For the case where only two partitions are requested:
      // We have emitted x1 as a partition, so just emit -x1 as the next one.
      // Note: maybe we can do better, but for now it is at least sound.
      // And there is no need to wait for another call to makePartitions to
      // execute this code.
      if (d_numPartitionsSoFar == 1)
      {
        *d_output << d_cubes[0] << "\n";
        NodeBuilder notBuilder2(kind::NOT);
        notBuilder2 << d_cubes[0];
        *d_output << notBuilder2.constructNode() << "\n";

        NodeBuilder notBuilder(kind::NOT);
        notBuilder << d_assertedLemmas.front();
        Node lemma = notBuilder.constructNode();
        return TrustNode::mkTrustLemma(lemma);
      }
      // If we ask for more than two partitions.
      else
      {
        // Last partition
        // Dump and assert the negation of the previous cubes

        // from i=1 to n where n is the number of requested cubes:
        // c1
        // !c1 &  c2
        // !c1 & !c2 &  c3
        // !c1 & !c2 & !c3
         NodeManager* nm = NodeManager::currentNM();
        for (int i = 0; i < d_numPartitions - 1; ++i)
        {
          vector<Node> stuff_to_and;
          for (int j = 0; j < i+1; ++j)
          {
            if (i == j)
            {
              stuff_to_and.push_back(d_cubes[j]);
              //cubeBuilder << d_cubes[j];
            }
            else
            {
              NodeBuilder cubeNotter(kind::NOT);
              cubeNotter << d_cubes[j];
              stuff_to_and.push_back(cubeNotter.constructNode());
            }
          }
          *d_output << nm->mkAnd(stuff_to_and) << "\n";

          //*d_output << cubeBuilder.constructNode() << "\n";
        }

        NodeBuilder cubeBuilder(kind::AND);
        for (int j = 0; j < d_numPartitions - 1; ++j)
        {
          NodeBuilder cubeNotter(kind::NOT);
          cubeNotter << d_cubes[j];
          cubeBuilder << cubeNotter.constructNode();
        }
        *d_output << cubeBuilder.constructNode() << "\n";

        // return a mktrust of false.
        NodeBuilder andBuilder(kind::AND);

        for (const auto d : d_assertedLemmas) andBuilder << d;
        Node conj = andBuilder.constructNode();
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
      if (options::decisionStrategy() == "old")
      {
        collectLiteralsOld(literals);
      }
      else
      {
        collectLiteralsNew(literals);
      }

      unsigned conflictSize = (unsigned)log2(d_numPartitions);
      if (literals.size() >= conflictSize)
      {
        std::vector<Node> tmpLiterals(literals.begin(),
                                      literals.begin() + conflictSize);
        Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
        d_cubes.push_back(conj);

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

// TODO !
   if (options::partitionStrategy() == "ll-to-all-revised"
        && d_numChecks >= options::numChecks())
   {
     if (d_numPartitionsSoFar == d_numPartitions - 1)
     {
       // Need to check if any of our cubes contain the negation of any of our learned literals.
       if (d_numPartitionsSoFar == 1)
       {
        auto learnedLits = d_propEngine->getLearnedZeroLevelLiterals();
         NodeManager* nm = NodeManager::currentNM();
         std::vector<Node> stuff_to_and;
        std::vector<Node> to_keep;
        bool subterm_issue = false;
          auto c1 = d_cubes[0]; 
         for (auto ll : learnedLits) { 
          if ((expr::hasSubterm(c1, ll))) { 
            subterm_issue = true;
            std::unordered_set<cvc5::Node> ts;
            expr::getSubterms(c1, true, ts) ;
            for (auto st : ts){ 
              if (st.getKind() == kind::NOT) { 
                if (learnedLits.count(st) != 0) {
                  to_keep.push_back(st);
                } 
              }
              else {
                if (learnedLits.count(st) != 0) {
                  to_keep.push_back(st);
                } 
                to_keep.push_back(st);
              }
            }
          }
         }

        if (to_keep.size() == 0 && subterm_issue == true) {
          d_numPartitionsSoFar--;
          d_cubes.erase(d_cubes.begin());
          // Now return something that won't hurt anything. 
         return TrustNode::mkTrustLemma(d_assertedLemmas.front());
        }
        else if (subterm_issue) {
         d_cubes[0] = nm->mkAnd(to_keep); 
        }

        for (auto ll : learnedLits) stuff_to_and.push_back(ll);
        stuff_to_and.push_back(d_cubes[0]);
        *d_output << nm->mkAnd(stuff_to_and) << "\n";

        std::vector<Node> stuff_to_and2;
        for (auto ll : d_propEngine->getLearnedZeroLevelLiterals()) stuff_to_and2.push_back(ll);
        NodeBuilder notBuilder2(kind::NOT);
        notBuilder2 << d_cubes[0];
        stuff_to_and2.push_back(notBuilder2.constructNode());
        *d_output << nm->mkAnd(stuff_to_and2) << "\n";

        NodeBuilder notBuilder(kind::NOT);
        notBuilder << d_assertedLemmas.front();
        Node lemma = notBuilder.constructNode();
        return TrustNode::mkTrustLemma(lemma);
       }
       // If we ask for more than two partitions.
       else
       {
          auto learnedLits = d_propEngine->getLearnedZeroLevelLiterals();
          NodeManager* nm = NodeManager::currentNM();
        
         for (int i = 0; i < d_numPartitions - 1; ++i)
         {
        // per cube
          std::vector<Node> stuff_to_and;
          std::vector<Node> to_keep;
          bool subterm_issue = false;

          // Replace with each cube. 
          auto c1 = d_cubes[i]; 

          for (auto ll : learnedLits) { 
            if ((expr::hasSubterm(c1, ll))) { 
              subterm_issue = true;
              std::unordered_set<cvc5::Node> ts;
              expr::getSubterms(c1, true, ts) ;
              for (auto st : ts){ 
                if (st.getKind() == kind::NOT) { 
                  if (learnedLits.count(st) != 0) {
                    to_keep.push_back(st);
                  } 
                }
                else {
                  if (learnedLits.count(st) != 0) {
                    to_keep.push_back(st);
                  } 
                  to_keep.push_back(st);
                }
              }
            } 
          }

          if (to_keep.size() == 0 && subterm_issue == true) {
            d_numPartitionsSoFar--;
            d_cubes.erase(d_cubes.begin());
          }
          else if (subterm_issue) {
           d_cubes[i] = nm->mkAnd(to_keep); 
          }
         }

          if (d_numPartitionsSoFar < d_numPartitions - 1) {
            return TrustNode::mkTrustLemma(d_assertedLemmas.front());
          }



         std::unordered_set<Node> learned_lits = d_propEngine->getLearnedZeroLevelLiterals();
         std::cout << "ll size " << learned_lits.size() << "\n";
         for (auto ll : learned_lits) std::cout << "learned lit " << ll <<std::endl;

         for (int i = 0; i < d_numPartitions - 1; ++i)
         {
           NodeBuilder cubeBuilder(kind::AND);
           cubeBuilder << d_cubes[i];
           for (Node ll : learned_lits)
           {
               cubeBuilder << ll;
           }
           *d_output << cubeBuilder.constructNode() << "\n";
         }

         NodeBuilder cubeBuilder(kind::AND);
         for (int j = 0; j < d_numPartitions - 1; ++j)
         {
           NodeBuilder cubeNotter(kind::NOT);
           cubeNotter << d_cubes[j];
           cubeBuilder << cubeNotter.constructNode();
         }
         *d_output << cubeBuilder.constructNode() << "\n";

        // Below is just returning stuff to make it unsat.
         // return a mktrust of false.
         NodeBuilder andBuilder(kind::AND);

         for (const auto d : d_assertedLemmas) andBuilder << d;
         Node conj = andBuilder.constructNode();
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
       if (options::decisionStrategy() == "old")
       {
         collectLiteralsOld(literals);
       }
       else
       {
         collectLiteralsNew(literals);
       }

       unsigned conflictSize = (unsigned)log2(d_numPartitions);
       if (literals.size() >= conflictSize)
       {
         std::vector<Node> tmpLiterals(literals.begin(),
                                       literals.begin() + conflictSize);
         Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
         d_cubes.push_back(conj);

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

  // Old way of doing things:
  // On each standard check, create a cube, e.g. x1 & x2 with at least
  // conflcitSize variables. Send the not of that cube, i.e. -x1 | -x2, to the
  // solver. After making n-1 cubes, e.g. you have made C1, C2, C3, emit the
  // final cube as -C1 | -C2 | -C3.
  if (options::partitionStrategy() == "old")
  {
    // If we're at the last cube
    if (d_numPartitionsSoFar == d_numPartitions - 1)
    {
      // For the case where only two partitions are requested:
      // We have emitted x1 as a partition, so just emit -x1 as the next one.
      // Note: maybe we can do better, but for now it is at least sound.
      // And there is no need to wait for another call to makePartitions to
      // execute this code.
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
        // Last partition
        // Dump and assert the negation of the previous cubes

        NodeBuilder orBuilder(kind::OR);

        // Make a trustnode of everything in list and call conflict.
        for (const auto d : d_assertedLemmas) orBuilder << d;

        // disj is an OR of all the previously asserted lemmas.
        // in other words, it is a disjunction of the negation of all the cubes.
        Node disj = orBuilder.constructNode();

        *d_output << disj << "\n";

        if (d_partitionFile != "")
        {
          d_partitionFileStream.close();
        }
        // return a mktrust of false.
        NodeBuilder andBuilder(kind::AND);

        for (const auto d : d_assertedLemmas) andBuilder << d;
        Node conj = andBuilder.constructNode();
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
      if (options::decisionStrategy() == "old")
      {
        collectLiteralsOld(literals);
      }
      else
      {
        collectLiteralsNew(literals);
      }

      /*
      If we don't emit any conflict, then the result is valid.
      completely naive way: this entire feature is finding one literal
      Split on it and recurse at the higher level.
      Does gg know which partitions are free?
      For any given problem, try solving it directly and also produce splits to
      try on other machines.
      Can this be made adaptive?
      Need to be able to make just one partition.
      */

      // This conflictSize is to make sure we get cubes with at least
      // a certain amount of literals.
      unsigned conflictSize = (unsigned)log2(d_numPartitions);
      if (literals.size() >= conflictSize)
      {
        // Make a trustnode of "everything" in literals and call conflict.

        // This is basically random right now.
        // Makes more sense to take the first n decisions instead.
        // TODO: expose interface to get the first n decisions from the solver.
        // This is getting the first conflictSize literals
        // which is in no particular order.
        // Why did we not use all the literals?
        std::vector<Node> tmpLiterals(literals.begin(),
                                      literals.begin() + conflictSize);
        Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
        // std::cout << "Not last cube" << std::endl;
        *d_output << conj << "\n";
        if (d_partitionFile != "")
        {
          d_partitionFileStream.close();
        }
        // std::cout << conj << "\n";
        // NodeBuilder andBuilder(kind::AND);
        // for (auto d : literals) andBuilder << d;
        // Node conj = andBuilder.constructNode();
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

// This has been replaced by "strict_cubes"
  // if (options::partitionStrategy() == "old-revised-improved")
  // {
  //   // If we're at the last cube
  //   if (d_numPartitionsSoFar == d_numPartitions - 1)
  //   {
  //     if (d_numPartitionsSoFar == 1)
  //     {
  //       *d_output << d_assertedLemmas.front() << "\n";
  //       NodeBuilder notBuilder(kind::NOT);
  //       notBuilder << d_assertedLemmas.front();
  //       Node lemma = notBuilder.constructNode();
  //       *d_output << lemma << "\n";
  //       return TrustNode::mkTrustLemma(lemma);
  //     }
  //     // If we ask for more than two partitions.
  //     else
  //     {
  //       // Emit
  //       // c1 & ~c2 & ~c3
  //       // c2 & ~c1 & ~c3
  //       // c3 & ~c1 & ~c2
  //       // ~c1 & ~c2 & ~c3

  //       vector<Node> cubes_to_emit;
  //       for (const auto d1 : d_assertedLemmas)
  //       {
  //         NodeBuilder andBuilder(kind::AND);
  //         for (const auto d2 : d_assertedLemmas)
  //         {
  //           if (d1 == d2)
  //           {
  //             andBuilder << d2;
  //           }
  //           else
  //           {
  //             NodeBuilder notBuilder(kind::NOT);
  //             notBuilder << d2;
  //             Node negated_cube = notBuilder.constructNode();
  //             andBuilder << negated_cube;
  //           }
  //         }
  //         cubes_to_emit.push_back(andBuilder.constructNode());
  //       }

  //       NodeBuilder andBuilder(kind::AND);
  //       for (const auto d : d_assertedLemmas)
  //       {
  //         NodeBuilder notBuilder(kind::NOT);
  //         notBuilder << d;
  //         Node negated_cube = notBuilder.constructNode();
  //         andBuilder << negated_cube;
  //       }
  //       cubes_to_emit.push_back(andBuilder.constructNode());

  //       for (const auto d : cubes_to_emit)
  //       {
  //         *d_output << d << "\n";
  //       }

  //       if (d_partitionFile != "")
  //       {
  //         d_partitionFileStream.close();
  //       }

  //       NodeBuilder andBuilder2(kind::AND);
  //       for (const auto d : d_assertedLemmas) andBuilder2 << d;
  //       Node conj = andBuilder2.constructNode();
  //       NodeBuilder notBuilder(kind::NOT);
  //       notBuilder << conj;
  //       Node lemma = notBuilder.constructNode();
  //       ++d_numPartitionsSoFar;

  //       return TrustNode::mkTrustLemma(lemma);
  //     }
  //   }

  //   // Not at the last cube
  //   else
  //   {
  //     std::vector<TNode> literals;
  //     if (options::decisionStrategy() == "old")
  //     {
  //       collectLiteralsOld(literals);
  //     }
  //     else
  //     {
  //       collectLiteralsNew(literals);
  //     }

  //     unsigned conflictSize = (unsigned)log2(d_numPartitions);
  //     if (literals.size() >= conflictSize)
  //     {
  //       std::vector<Node> tmpLiterals(literals.begin(),
  //                                     literals.begin() + conflictSize);
  //       Node conj = NodeManager::currentNM()->mkAnd(tmpLiterals);
  //       // *d_output << conj << "\n";
  //       // if (d_partitionFile != "")
  //       //{
  //       //  d_partitionFileStream.close();
  //       //}

  //       NodeBuilder notBuilder(kind::NOT);
  //       notBuilder << conj;
  //       Node lemma = notBuilder.constructNode();

  //       ++d_numPartitionsSoFar;
  //       d_assertedLemmas.push_back(lemma);

  //       TrustNode trustedLemma = TrustNode::mkTrustLemma(lemma);
  //       return trustedLemma;
  //     }
  //   }

  //   if (d_partitionFile != "")
  //   {
  //     d_partitionFileStream.close();
  //   }

  //   return TrustNode::null();
  // }

  // TODO: add learned literals as an option to all partitioning strategies. 
  if (options::partitionStrategy() == "old-revised-ll")
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
      if (options::decisionStrategy() == "old")
      {
        collectLiteralsOld(literals);
      }
      else
      {
        collectLiteralsNew(literals);
      }

      unsigned conflictSize = (unsigned)log2(d_numPartitions);
      if (literals.size() >= conflictSize)
      {
        std::vector<Node> tmpLiterals(literals.begin(),
                                      literals.begin() + conflictSize);
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

  if (options::partitionStrategy() == "old-revised")
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
      if (options::decisionStrategy() == "old")
      {
        collectLiteralsOld(literals);
      }
      else
      {
        collectLiteralsNew(literals);
      }

      unsigned conflictSize = (unsigned)log2(d_numPartitions);
      if (literals.size() >= conflictSize)
      {
        std::vector<Node> tmpLiterals(literals.begin(),
                                      literals.begin() + conflictSize);
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

  // This splits on each variable in the decision trail.
  if (options::partitionStrategy() == "full-trail"
      && d_numChecks >= options::numChecks())
  {
    std::vector<TNode> literals;
    if (options::decisionStrategy() == "old")
    {
      collectLiteralsOld(literals);
    }
    else
    {
      collectLiteralsNew(literals);
    }

    unsigned conflictSize = (unsigned)log2(d_numPartitions);
    if (literals.size() >= conflictSize)
    {
      std::vector<Node> tmpLiterals(literals.begin(),
                                    literals.begin() + conflictSize);
      std::vector<Node> part_nodes;
      int part_depth = conflictSize;

      // This complicated thing is basically making a truth table
      // of length 2^depth so that these can be put together into a partition
      // later.
      std::vector<std::vector<Node> > result_node_lists(pow(2, part_depth));
      std::vector<std::vector<std::string> > testv(pow(2, part_depth));
      int i = 1;
      bool t = false;
      int q = part_depth;
      for (Node n : tmpLiterals)
      {
        NodeBuilder notBuilder(kind::NOT);
        notBuilder << n;
        Node lemma = notBuilder.constructNode();
        int total = pow(2, part_depth);
        q = q - 1;
        int loc = 0;
        for (int z = 0; z < total / pow(2, q); ++z)
        {
          t = !t;
          for (int j = 0; j < total; ++j)
          {
            if (j < pow(2, q))
            {
              result_node_lists[loc].push_back((t ? n : lemma));
              ;
              ++loc;
            }
          }
        }
      }
      for (std::vector<Node> lst : result_node_lists)
      {
        Node conj = NodeManager::currentNM()->mkAnd(lst);
        *d_output << conj << std::endl;
      }

      if (d_partitionFile != "")
      {
        d_partitionFileStream.close();
      }
    }
    if (literals.size() >= conflictSize)
    {
      NodeBuilder notBuilder(kind::NOT);
      notBuilder << literals.front();
      Node nl = notBuilder.constructNode();
      std::vector<Node> f;
      f.push_back(literals.front());
      f.push_back(nl);
      Node fals = NodeManager::currentNM()->mkAnd(f);

      TrustNode trustedLemma = TrustNode::mkTrustLemma(fals);
      return trustedLemma;
    }
    return TrustNode::null();
  }
  return TrustNode::null();
}

}  // namespace theory
}  // namespace cvc5

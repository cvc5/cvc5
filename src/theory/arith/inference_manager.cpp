/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Gereon Kremer, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the inference manager for the theory of strings.
 **/

#include "theory/arith/inference_manager.h"

#include "options/arith_options.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

InferenceManager::InferenceManager(TheoryArith& ta,
                                   ArithState& astate,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(ta, astate, pnm)
{
}

void InferenceManager::addPendingArithLemma(std::unique_ptr<ArithLemma> lemma,
                                            bool isWaiting)
{
  Trace("arith::infman") << "Add " << lemma->d_inference << " " << lemma->d_node
                         << (isWaiting ? " as waiting" : "") << std::endl;
  if (hasCachedLemma(lemma->d_node, lemma->d_property))
  {
    return;
  }
  if (isEntailedFalse(*lemma))
  {
    if (isWaiting)
    {
      d_waitingLem.clear();
    }
    else
    {
      d_pendingLem.clear();
      d_theoryState.notifyInConflict();
    }
  }
  if (isWaiting)
  {
    d_waitingLem.emplace_back(std::move(lemma));
  }
  else
  {
    d_pendingLem.emplace_back(std::move(lemma));
  }
}
void InferenceManager::addPendingArithLemma(const ArithLemma& lemma,
                                            bool isWaiting)
{
  addPendingArithLemma(std::unique_ptr<ArithLemma>(new ArithLemma(lemma)),
                       isWaiting);
}
void InferenceManager::addPendingArithLemma(const Node& lemma,
                                            InferenceId inftype,
                                            ProofGenerator* pg,
                                            bool isWaiting,
                                            LemmaProperty p)
{
  addPendingArithLemma(
      std::unique_ptr<ArithLemma>(new ArithLemma(lemma, p, pg, inftype)),
      isWaiting);
}

void InferenceManager::flushWaitingLemmas()
{
  for (auto& lem : d_waitingLem)
  {
    Trace("arith::infman") << "Flush waiting lemma to pending: "
                           << lem->d_inference << " " << lem->d_node
                           << std::endl;
    d_pendingLem.emplace_back(std::move(lem));
  }
  d_waitingLem.clear();
}
void InferenceManager::clearWaitingLemmas()
{
  d_waitingLem.clear();
}

bool InferenceManager::hasUsed() const
{
  return hasSent() || hasPending();
}

bool InferenceManager::hasWaitingLemma() const
{
  return !d_waitingLem.empty();
}

std::size_t InferenceManager::numWaitingLemmas() const
{
  return d_waitingLem.size();
}

bool InferenceManager::hasCachedLemma(TNode lem, LemmaProperty p)
{
  Node rewritten = Rewriter::rewrite(lem);
  return TheoryInferenceManager::hasCachedLemma(rewritten, p);
}

bool InferenceManager::cacheLemma(TNode lem, LemmaProperty p)
{
  Node rewritten = Rewriter::rewrite(lem);
  return TheoryInferenceManager::cacheLemma(rewritten, p);
}

bool InferenceManager::isEntailedFalse(const ArithLemma& lem)
{
  if (options::nlExtEntailConflicts())
  {
    Node ch_lemma = lem.d_node.negate();
    ch_lemma = Rewriter::rewrite(ch_lemma);
    Trace("arith-inf-manager") << "InferenceManager::Check entailment of "
                               << ch_lemma << "..." << std::endl;

    std::pair<bool, Node> et = d_theory.getValuation().entailmentCheck(
        options::TheoryOfMode::THEORY_OF_TYPE_BASED, ch_lemma);
    Trace("arith-inf-manager") << "entailment test result : " << et.first << " "
                               << et.second << std::endl;
    if (et.first)
    {
      Trace("arith-inf-manager")
          << "*** Lemma entailed to be in conflict : " << lem.d_node
          << std::endl;
      return true;
    }
  }
  return false;
}

}  // namespace arith
}  // namespace theory
}  // namespace CVC4

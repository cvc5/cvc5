/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Makai Mann, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the inference manager for the theory of strings.
 */

#include "theory/arith/inference_manager.h"

#include "options/arith_options.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/theory_arith.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace arith {

InferenceManager::InferenceManager(TheoryArith& ta,
                                   ArithState& astate,
                                   ProofNodeManager* pnm)
    : InferenceManagerBuffered(ta, astate, pnm, "theory::arith::")
{
}

void InferenceManager::addPendingLemma(std::unique_ptr<SimpleTheoryLemma> lemma,
                                       bool isWaiting)
{
  Trace("arith::infman") << "Add " << lemma->getId() << " " << lemma->d_node
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
void InferenceManager::addPendingLemma(const SimpleTheoryLemma& lemma,
                                       bool isWaiting)
{
  addPendingLemma(
      std::unique_ptr<SimpleTheoryLemma>(new SimpleTheoryLemma(lemma)),
      isWaiting);
}
void InferenceManager::addPendingLemma(const Node& lemma,
                                       InferenceId inftype,
                                       ProofGenerator* pg,
                                       bool isWaiting,
                                       LemmaProperty p)
{
  addPendingLemma(std::unique_ptr<SimpleTheoryLemma>(
                      new SimpleTheoryLemma(inftype, lemma, p, pg)),
                  isWaiting);
}

void InferenceManager::flushWaitingLemmas()
{
  for (auto& lem : d_waitingLem)
  {
    Trace("arith::infman") << "Flush waiting lemma to pending: "
                           << lem->getId() << " " << lem->d_node
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

bool InferenceManager::isEntailedFalse(const SimpleTheoryLemma& lem)
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
}  // namespace cvc5

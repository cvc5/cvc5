/*********************                                                        */
/*! \file inference_manager_buffered.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A buffered inference manager
 **/

#include "theory/inference_manager_buffered.h"

#include "theory/rewriter.h"
#include "theory/theory.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

InferenceManagerBuffered::InferenceManagerBuffered(Theory& t,
                                                   TheoryState& state,
                                                   ProofNodeManager* pnm)
    : TheoryInferenceManager(t, state, pnm), d_processingPendingLemmas(false)
{
}

bool InferenceManagerBuffered::hasPending() const
{
  return hasPendingFact() || hasPendingLemma();
}

bool InferenceManagerBuffered::hasPendingFact() const
{
  return !d_pendingFact.empty();
}

bool InferenceManagerBuffered::hasPendingLemma() const
{
  return !d_pendingLem.empty();
}

bool InferenceManagerBuffered::addPendingLemma(Node lem,
                                               LemmaProperty p,
                                               ProofGenerator* pg,
                                               bool checkCache)
{
  if (checkCache)
  {
    // check if it is unique up to rewriting
    Node lemr = Rewriter::rewrite(lem);
    if (hasCachedLemma(lemr, p))
    {
      return false;
    }
  }
  // make the simple theory lemma
  d_pendingLem.emplace_back(new SimpleTheoryLemma(lem, p, pg));
  return true;
}

void InferenceManagerBuffered::addPendingLemma(
    std::unique_ptr<TheoryInference> lemma)
{
  d_pendingLem.emplace_back(std::move(lemma));
}

void InferenceManagerBuffered::addPendingFact(Node conc,
                                              Node exp,
                                              ProofGenerator* pg)
{
  // make a simple theory internal fact
  Assert(conc.getKind() != AND && conc.getKind() != OR);
  d_pendingFact.emplace_back(new SimpleTheoryInternalFact(conc, exp, pg));
}

void InferenceManagerBuffered::addPendingFact(
    std::unique_ptr<TheoryInference> fact)
{
  d_pendingFact.emplace_back(std::move(fact));
}

void InferenceManagerBuffered::addPendingPhaseRequirement(Node lit, bool pol)
{
  // it is the responsibility of the caller to ensure lit is rewritten
  d_pendingReqPhase[lit] = pol;
}

void InferenceManagerBuffered::doPendingFacts()
{
  size_t i = 0;
  while (!d_theoryState.isInConflict() && i < d_pendingFact.size())
  {
    // process this fact, which notice may enqueue more pending facts in this
    // loop.
    d_pendingFact[i]->process(this, false);
    i++;
  }
  d_pendingFact.clear();
}

void InferenceManagerBuffered::doPendingLemmas()
{
  if (d_processingPendingLemmas)
  {
    // already processing
    return;
  }
  d_processingPendingLemmas = true;
  size_t i = 0;
  while (i < d_pendingLem.size())
  {
    // process this lemma, which notice may enqueue more pending lemmas in this
    // loop, or clear the lemmas.
    d_pendingLem[i]->process(this, true);
    i++;
  }
  d_pendingLem.clear();
  d_processingPendingLemmas = false;
}

void InferenceManagerBuffered::doPendingPhaseRequirements()
{
  // process the pending require phase calls
  for (const std::pair<const Node, bool>& prp : d_pendingReqPhase)
  {
    requirePhase(prp.first, prp.second);
  }
  d_pendingReqPhase.clear();
}
void InferenceManagerBuffered::clearPending()
{
  d_pendingFact.clear();
  d_pendingLem.clear();
  d_pendingReqPhase.clear();
}
void InferenceManagerBuffered::clearPendingFacts() { d_pendingFact.clear(); }
void InferenceManagerBuffered::clearPendingLemmas() { d_pendingLem.clear(); }
void InferenceManagerBuffered::clearPendingPhaseRequirements()
{
  d_pendingReqPhase.clear();
}


  std::size_t InferenceManagerBuffered::numPendingLemmas() const {
    return d_pendingLem.size();
  }
  std::size_t InferenceManagerBuffered::numPendingFacts() const {
    return d_pendingFact.size();
  }

}  // namespace theory
}  // namespace CVC4

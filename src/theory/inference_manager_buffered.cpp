/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A buffered inference manager.
 */

#include "theory/inference_manager_buffered.h"

#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

InferenceManagerBuffered::InferenceManagerBuffered(Env& env,
                                                   Theory& t,
                                                   TheoryState& state,
                                                   const std::string& statsName,
                                                   bool cacheLemmas)
    : TheoryInferenceManager(env, t, state, statsName, cacheLemmas),
      d_processingPendingLemmas(false)
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
                                               InferenceId id,
                                               LemmaProperty p,
                                               ProofGenerator* pg,
                                               bool checkCache)
{
  if (checkCache)
  {
    // check if it is unique up to rewriting
    Node lemr = rewrite(lem);
    if (hasCachedLemma(lemr, p))
    {
      return false;
    }
  }
  // make the simple theory lemma
  d_pendingLem.emplace_back(new SimpleTheoryLemma(id, lem, p, pg));
  return true;
}

void InferenceManagerBuffered::addPendingLemma(
    std::unique_ptr<TheoryInference> lemma)
{
  d_pendingLem.emplace_back(std::move(lemma));
}

void InferenceManagerBuffered::addPendingFact(Node conc,
                                              InferenceId id,
                                              Node exp,
                                              ProofGenerator* pg)
{
  // make a simple theory internal fact
  Assert(conc.getKind() != AND && conc.getKind() != OR);
  d_pendingFact.emplace_back(new SimpleTheoryInternalFact(id, conc, exp, pg));
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
    // assert the internal fact, which notice may enqueue more pending facts in
    // this loop, or result in a conflict.
    assertInternalFactTheoryInference(d_pendingFact[i].get());
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
    lemmaTheoryInference(d_pendingLem[i].get());
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

std::size_t InferenceManagerBuffered::numPendingLemmas() const
{
  return d_pendingLem.size();
}
std::size_t InferenceManagerBuffered::numPendingFacts() const
{
  return d_pendingFact.size();
}

bool InferenceManagerBuffered::lemmaTheoryInference(TheoryInference* lem)
{
  // process this lemma
  LemmaProperty p = LemmaProperty::NONE;
  TrustNode tlem = lem->processLemma(p);
  Assert(!tlem.isNull());
  // send the lemma
  return trustedLemma(tlem, lem->getId(), p);
}

void InferenceManagerBuffered::assertInternalFactTheoryInference(
    TheoryInference* fact)
{
  // process this fact
  std::vector<Node> exp;
  ProofGenerator* pg = nullptr;
  Node lit = fact->processFact(exp, pg);
  Assert(!lit.isNull());
  bool pol = lit.getKind() != NOT;
  TNode atom = pol ? lit : lit[0];
  // no double negation or conjunctive conclusions
  Assert(atom.getKind() != NOT && atom.getKind() != AND);
  // assert the internal fact
  assertInternalFact(atom, pol, fact->getId(), exp, pg);
}

void InferenceManagerBuffered::notifyInConflict()
{
  d_theoryState.notifyInConflict();
  // also clear the pending facts, which will be stale after backtracking
  clearPending();
}

}  // namespace theory
}  // namespace cvc5::internal

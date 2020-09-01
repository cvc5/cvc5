/*********************                                                        */
/*! \file inference_manager_buffered.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
    : TheoryInferenceManager(t, state, pnm)
{
}

bool InferenceManagerBuffered::hasProcessed() const
{
  return d_theoryState.isInConflict() || !d_pendingLem.empty()
         || !d_pendingFact.empty();
}

bool InferenceManagerBuffered::hasPendingFact() const
{
  return !d_pendingFact.empty();
}

bool InferenceManagerBuffered::hasPendingLemma() const
{
  return !d_pendingLem.empty();
}

void InferenceManagerBuffered::addPendingLemma(Node lem,
                                               LemmaProperty p,
                                               ProofGenerator* pg)
{
  // make the simple theory lemma
  d_pendingLem.push_back(std::make_shared<SimpleTheoryLemma>(lem, p, pg));
}

void InferenceManagerBuffered::addPendingLemma(
    std::shared_ptr<TheoryInference> lemma)
{
  d_pendingLem.emplace_back(std::move(lemma));
}

void InferenceManagerBuffered::addPendingFact(Node fact,
                                              Node exp,
                                              ProofGenerator* pg)
{
  Assert(fact.getKind() != AND && fact.getKind() != OR);
  d_pendingFact.push_back(std::pair<Node, Node>(fact, exp));
}

void InferenceManagerBuffered::addPendingPhaseRequirement(Node lit, bool pol)
{
  // must ensure rewritten
  lit = Rewriter::rewrite(lit);
  d_pendingReqPhase[lit] = pol;
}

void InferenceManagerBuffered::doPendingFacts()
{
  size_t i = 0;
  while (!d_theoryState.isInConflict() && i < d_pendingFact.size())
  {
    std::pair<Node, Node>& pfact = d_pendingFact[i];
    Node fact = pfact.first;
    Node exp = pfact.second;
    bool polarity = fact.getKind() != NOT;
    TNode atom = polarity ? fact : fact[0];
    // no double negation or conjunctive conclusions
    Assert(atom.getKind() != NOT && atom.getKind() != AND);
    assertInternalFact(atom, polarity, exp);
    i++;
  }
  d_pendingFact.clear();
}

void InferenceManagerBuffered::doPendingLemmas()
{
  // process all the pending lemmas
  for (const std::shared_ptr<TheoryInference>& plem : d_pendingLem)
  {
    // process the inference
    plem->process(this);
  }
  d_pendingLem.clear();
}

void InferenceManagerBuffered::doPendingPhaseRequirements()
{
  // process the pending require phase calls
  for (const std::pair<const Node, bool>& prp : d_pendingReqPhase)
  {
    d_out.requirePhase(prp.first, prp.second);
  }
  d_pendingReqPhase.clear();
}
void InferenceManagerBuffered::clearPendingFacts() { d_pendingFact.clear(); }
void InferenceManagerBuffered::clearPendingLemmas() { d_pendingLem.clear(); }
void InferenceManagerBuffered::clearPendingPhaseRequirements()
{
  d_pendingReqPhase.clear();
}

}  // namespace theory
}  // namespace CVC4

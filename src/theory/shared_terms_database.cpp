/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/shared_terms_database.h"

#include "options/theory_options.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace cvc5::internal::theory;

namespace cvc5::internal {

SharedTermsDatabase::SharedTermsDatabase(Env& env, TheoryEngine* theoryEngine)
    : EnvObj(env),
      ContextNotifyObj(env.getContext()),
      d_statSharedTerms(
          statisticsRegistry().registerInt("theory::shared_terms")),
      d_addedSharedTermsSize(env.getContext(), 0),
      d_termsToTheories(env.getContext()),
      d_alreadyNotifiedMap(env.getContext()),
      d_registeredEqualities(env.getContext()),
      d_EENotify(*this),
      d_theoryEngine(theoryEngine),
      d_inConflict(env.getContext(), false),
      d_conflictPolarity(),
      d_equalityEngine(nullptr),
      d_pfee(nullptr),
      d_out(theoryEngine->theoryOf(THEORY_BUILTIN)->getOutputChannel())
{
}

void SharedTermsDatabase::setEqualityEngine(eq::EqualityEngine* ee)
{
  Assert(ee != nullptr);
  d_equalityEngine = ee;
  // if proofs are enabled, make the proof equality engine if necessary
  if (d_env.isTheoryProofProducing())
  {
    d_pfee = d_equalityEngine->getProofEqualityEngine();
    if (d_pfee == nullptr)
    {
      d_pfeeAlloc = std::make_unique<eq::ProofEqEngine>(d_env, *ee);
      d_pfee = d_pfeeAlloc.get();
      d_equalityEngine->setProofEqualityEngine(d_pfee);
    }
  }
}

bool SharedTermsDatabase::needsEqualityEngine(EeSetupInfo& esi)
{
  esi.d_notify = &d_EENotify;
  esi.d_name = "shared::ee";
  return true;
}

void SharedTermsDatabase::addEqualityToPropagate(TNode equality) {
  Assert(d_equalityEngine != nullptr);
  d_registeredEqualities.insert(equality);
  if (d_theoryEngine->hasSatValue(equality))
  {
    // don't need to propagate what is already asserted
    return;
  }
  d_equalityEngine->addTriggerPredicate(equality);
  checkForConflict();
}

void SharedTermsDatabase::addSharedTerm(TNode atom,
                                        TNode term,
                                        TheoryIdSet theories)
{
  Trace("register") << "SharedTermsDatabase::addSharedTerm(" << atom << ", "
                    << term << ", " << TheoryIdSetUtil::setToString(theories)
                    << ")" << std::endl;

  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  if (find == d_termsToTheories.end()) {
    // First time for this term and this atom
    d_atomsToTerms[atom].push_back(term);
    d_addedSharedTerms.push_back(atom);
    d_addedSharedTermsSize = d_addedSharedTermsSize + 1;
    d_termsToTheories[search_pair] = theories;
  } else {
    Assert(theories != (*find).second);
    d_termsToTheories[search_pair] =
        TheoryIdSetUtil::setUnion(theories, (*find).second);
  }
}

SharedTermsDatabase::shared_terms_iterator SharedTermsDatabase::begin(TNode atom) const {
  Assert(hasSharedTerms(atom));
  return d_atomsToTerms.find(atom)->second.begin();
}

SharedTermsDatabase::shared_terms_iterator SharedTermsDatabase::end(TNode atom) const {
  Assert(hasSharedTerms(atom));
  return d_atomsToTerms.find(atom)->second.end();
}

bool SharedTermsDatabase::hasSharedTerms(TNode atom) const {
  return d_atomsToTerms.find(atom) != d_atomsToTerms.end();
}

void SharedTermsDatabase::backtrack() {
  for (int i = d_addedSharedTerms.size() - 1, i_end = (int)d_addedSharedTermsSize; i >= i_end; -- i) {
    TNode atom = d_addedSharedTerms[i];
    shared_terms_list& list = d_atomsToTerms[atom];
    list.pop_back();
    if (list.empty()) {
      d_atomsToTerms.erase(atom);
    }
  }
  d_addedSharedTerms.resize(d_addedSharedTermsSize);
}

TheoryIdSet SharedTermsDatabase::getTheoriesToNotify(TNode atom,
                                                     TNode term) const
{
  // Get the theories that share this term from this atom
  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  Assert(find != d_termsToTheories.end());

  // Get the theories that were already notified
  TheoryIdSet alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }

  // Return the ones that haven't been notified yet
  return TheoryIdSetUtil::setDifference((*find).second, alreadyNotified);
}

TheoryIdSet SharedTermsDatabase::getNotifiedTheories(TNode term) const
{
  // Get the theories that were already notified
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    return (*theoriesFind).second;
  } else {
    return 0;
  }
}

bool SharedTermsDatabase::propagateSharedEquality(TheoryId theory, TNode a, TNode b, bool value)
{
  Trace("shared-terms-database") << "SharedTermsDatabase::newEquality(" << theory << "," << a << "," << b << ", " << (value ? "true" : "false") << ")" << endl;

  if (d_inConflict) {
    return false;
  }

  // Propagate away
  Node equality = a.eqNode(b);
  if (value) {
    d_theoryEngine->assertToTheory(equality, equality, theory, THEORY_BUILTIN);
  } else {
    d_theoryEngine->assertToTheory(equality.notNode(), equality.notNode(), theory, THEORY_BUILTIN);
  }

  // As you were
  return true;
}

void SharedTermsDatabase::markNotified(TNode term, TheoryIdSet theories)
{
  // Find out if there are any new theories that were notified about this term
  TheoryIdSet alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }
  TheoryIdSet newlyNotified =
      TheoryIdSetUtil::setDifference(theories, alreadyNotified);

  // If no new theories were notified, we are done
  if (newlyNotified == 0) {
    return;
  }

  Trace("shared-terms-database") << "SharedTermsDatabase::markNotified(" << term << ")" << endl;

  // First update the set of notified theories for this term
  d_alreadyNotifiedMap[term] =
      TheoryIdSetUtil::setUnion(newlyNotified, alreadyNotified);

  if (d_equalityEngine == nullptr)
  {
    // if we are not assigned an equality engine, there is nothing to do
    return;
  }

  // Mark the shared terms in the equality engine
  theory::TheoryId currentTheory;
  while ((currentTheory = TheoryIdSetUtil::setPop(newlyNotified))
         != THEORY_LAST)
  {
    d_equalityEngine->addTriggerTerm(term, currentTheory);
  }

  // Check for any conflits
  checkForConflict();
}

bool SharedTermsDatabase::areEqual(TNode a, TNode b) const {
  Assert(d_equalityEngine != nullptr);
  if (d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b))
  {
    return d_equalityEngine->areEqual(a, b);
  } else {
    Assert(d_equalityEngine->hasTerm(a) || a.isConst());
    Assert(d_equalityEngine->hasTerm(b) || b.isConst());
    // since one (or both) of them is a constant, and the other is in the equality engine, they are not same
    return false;
  }
}

bool SharedTermsDatabase::areDisequal(TNode a, TNode b) const {
  Assert(d_equalityEngine != nullptr);
  if (d_equalityEngine->hasTerm(a) && d_equalityEngine->hasTerm(b))
  {
    return d_equalityEngine->areDisequal(a, b, false);
  } else {
    Assert(d_equalityEngine->hasTerm(a) || a.isConst());
    Assert(d_equalityEngine->hasTerm(b) || b.isConst());
    // one (or both) are in the equality engine
    return false;
  }
}

theory::eq::EqualityEngine* SharedTermsDatabase::getEqualityEngine()
{
  return d_equalityEngine;
}

void SharedTermsDatabase::assertShared(TNode n, bool polarity, TNode reason)
{
  Assert(d_equalityEngine != nullptr);
  Trace("shared-terms-database::assert")
      << "SharedTermsDatabase::assertShared(" << n << ", "
      << (polarity ? "true" : "false") << ", " << reason << ")" << endl;
  // Add it to the equality engine
  if (n.getKind() == kind::EQUAL)
  {
    d_equalityEngine->assertEquality(n, polarity, reason);
  }
  else
  {
    d_equalityEngine->assertPredicate(n, polarity, reason);
  }
  // Check for conflict
  checkForConflict();
}

bool SharedTermsDatabase::propagateEquality(TNode equality, bool polarity) {
  if (polarity) {
    return d_out.propagate(equality);
  }
  return d_out.propagate(equality.notNode());
}

void SharedTermsDatabase::checkForConflict()
{
  if (!d_inConflict)
  {
    return;
  }
  d_inConflict = false;
  TrustNode trnc;
  if (d_pfee != nullptr)
  {
    Node conflict = d_conflictLHS.eqNode(d_conflictRHS);
    conflict = d_conflictPolarity ? conflict : conflict.notNode();
    trnc = d_pfee->assertConflict(conflict);
  }
  else
  {
    // standard explain
    std::vector<TNode> assumptions;
    d_equalityEngine->explainEquality(
        d_conflictLHS, d_conflictRHS, d_conflictPolarity, assumptions);
    Node conflictNode = NodeManager::currentNM()->mkAnd(assumptions);
    trnc = TrustNode::mkTrustConflict(conflictNode, nullptr);
  }
  d_theoryEngine->conflict(trnc, THEORY_BUILTIN);
  d_conflictLHS = d_conflictRHS = Node::null();
}

bool SharedTermsDatabase::isKnown(TNode literal) const {
  Assert(d_equalityEngine != nullptr);
  bool polarity = literal.getKind() != kind::NOT;
  TNode equality = polarity ? literal : literal[0];
  if (polarity) {
    return d_equalityEngine->areEqual(equality[0], equality[1]);
  } else {
    return d_equalityEngine->areDisequal(equality[0], equality[1], false);
  }
}

TrustNode SharedTermsDatabase::explain(TNode literal) const
{
  if (d_pfee != nullptr)
  {
    // use the proof equality engine if it exists
    return d_pfee->explain(literal);
  }
  // otherwise, explain without proofs
  Node exp = d_equalityEngine->mkExplainLit(literal);
  // no proof generator
  return TrustNode::mkTrustPropExp(literal, exp, nullptr);
}

}  // namespace cvc5::internal

/*********************                                                        */
/*! \file shared_terms_database.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/shared_terms_database.h"

using namespace std;
using namespace CVC4;
using namespace theory;

SharedTermsDatabase::SharedTermsDatabase(SharedTermsNotifyClass& notify, context::Context* context)
  : ContextNotifyObj(context),
    d_context(context), 
    d_statSharedTerms("theory::shared_terms", 0),
    d_addedSharedTermsSize(context, 0),
    d_termsToTheories(context),
    d_alreadyNotifiedMap(context),
    d_sharedNotify(notify),
    d_termToNotifyList(context),
    d_allocatedNLSize(0),
    d_allocatedNLNext(context, 0),
    d_EENotify(*this),
    d_equalityEngine(d_EENotify, context, "SharedTermsDatabase")
{
  StatisticsRegistry::registerStat(&d_statSharedTerms);
}

SharedTermsDatabase::~SharedTermsDatabase() throw(AssertionException)
{
  StatisticsRegistry::unregisterStat(&d_statSharedTerms);
  for (unsigned i = 0; i < d_allocatedNLSize; ++i) {
    d_allocatedNL[i]->deleteSelf();
  }
}

void SharedTermsDatabase::addSharedTerm(TNode atom, TNode term, Theory::Set theories) {
  Debug("register") << "SharedTermsDatabase::addSharedTerm(" << atom << ", " << term << ", " << Theory::setToString(theories) << ")" << std::endl; 

  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  if (find == d_termsToTheories.end()) {
    // First time for this term and this atom
    d_atomsToTerms[atom].push_back(term);
    d_addedSharedTerms.push_back(atom);
    d_addedSharedTermsSize = d_addedSharedTermsSize + 1;
    d_termsToTheories[search_pair] = theories;
    if (!d_equalityEngine.hasTerm(term)) {
      d_equalityEngine.addTriggerTerm(term);
    }
  } else {
    Assert(theories != (*find).second);
    d_termsToTheories[search_pair] = Theory::setUnion(theories, (*find).second); 
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

Theory::Set SharedTermsDatabase::getTheoriesToNotify(TNode atom, TNode term) const {
  // Get the theories that share this term from this atom 
  std::pair<TNode, TNode> search_pair(atom, term);
  SharedTermsTheoriesMap::iterator find = d_termsToTheories.find(search_pair);
  Assert(find != d_termsToTheories.end());  
  
  // Get the theories that were already notified
  Theory::Set alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }
  
  // Return the ones that haven't been notified yet
  return Theory::setDifference((*find).second, alreadyNotified);
}


Theory::Set SharedTermsDatabase::getNotifiedTheories(TNode term) const {
  // Get the theories that were already notified
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    return (*theoriesFind).second;
  } else {
    return 0;
  }
}


SharedTermsDatabase::NotifyList* SharedTermsDatabase::getNewNotifyList()
{
  NotifyList* retval;
  if (d_allocatedNLSize == d_allocatedNLNext) {
    retval = new (true) NotifyList(d_context);
    d_allocatedNL.push_back(retval);
    d_allocatedNLNext = ++d_allocatedNLSize;
  }
  else {
    retval = d_allocatedNL[d_allocatedNLNext];
    d_allocatedNLNext = d_allocatedNLNext + 1;
  }
  Assert(retval->empty());
  return retval;
}


void SharedTermsDatabase::mergeSharedTerms(TNode a, TNode b)
{
  // Note: a is the new representative
  Debug("shared-terms-database") << "SharedTermsDatabase::mergeSharedTerms(" << a << "," << b << ")" << endl;

  NotifyList* pnlLeft = NULL;
  NotifyList* pnlRight = NULL;

  TermToNotifyList::iterator it = d_termToNotifyList.find(a);
  if (it == d_termToNotifyList.end()) {
    pnlLeft = getNewNotifyList();
    d_termToNotifyList[a] = pnlLeft;
  }
  else {
    pnlLeft = (*it).second;
  }
  it = d_termToNotifyList.find(b);
  if (it != d_termToNotifyList.end()) {
    pnlRight = (*it).second;
  }

  // Get theories interested in EC for lhs
  Theory::Set lhsSet = getNotifiedTheories(a);
  Theory::Set rhsSet = getNotifiedTheories(b);
  NotifyList::iterator nit;
  TNode left, right;

  for (TheoryId currentTheory = THEORY_FIRST; currentTheory != THEORY_LAST; ++ currentTheory) {

    if (Theory::setContains(currentTheory, rhsSet)) {
      right = b;
    }
    else if (pnlRight != NULL &&
             ((nit = pnlRight->find(currentTheory)) != pnlRight->end())) {
      right = (*nit).second;
    }
    else {
      // no match for right: continue
      continue;
    }

    if (Theory::setContains(currentTheory, lhsSet)) {
      left = a;
    }
    else if ((nit = pnlLeft->find(currentTheory)) != pnlLeft->end()) {
      left = (*nit).second;
    }
    else {
      // no match for left: insert right into left
      (*pnlLeft)[currentTheory] = right;
      continue;
    }

    // New shared equality: notify the client

    // TODO: add propagation of disequalities?

    assertEq(left.eqNode(right), currentTheory);
  }

}
  

void SharedTermsDatabase::assertEq(TNode equality, TheoryId theory)
{
  Debug("shared-terms-database") << "SharedTermsDatabase::assertEq(" << equality << ") to theory " << theory << endl;
  Node normalized = Rewriter::rewriteEquality(theory, equality);
  if (normalized.getKind() != kind::CONST_BOOLEAN || !normalized.getConst<bool>()) {
    // Notify client
    d_sharedNotify.notify(normalized, equality, theory);
  }
}


// term was just part of an assertion that makes it shared for theories
// Let's mark that the set theories has now been notified
// In addition, we make sure the equivalence class containing term knows a
// representative for each theory in theories.
// Finally, if the EC already knows a rep for a theory that was just notified, we
// have to tell the theory that these two terms are equal.
void SharedTermsDatabase::markNotified(TNode term, Theory::Set theories) {

  // Find out if there are any new theories that were notified about this term
  Theory::Set alreadyNotified = 0;
  AlreadyNotifiedMap::iterator theoriesFind = d_alreadyNotifiedMap.find(term);
  if (theoriesFind != d_alreadyNotifiedMap.end()) {
    alreadyNotified = (*theoriesFind).second;
  }
  Theory::Set newlyNotified = Theory::setDifference(theories, alreadyNotified);

  // If no new theories were notified, we are done
  if (newlyNotified == 0) {
    return;
  }

  Debug("shared-terms-database") << "SharedTermsDatabase::markNotified(" << term << ")" << endl;

  // First update the set of notified theories for this term
  d_alreadyNotifiedMap[term] = Theory::setUnion(newlyNotified, alreadyNotified);

  // Now get the representative of the equivalence class and find out which theories it represents
  TNode rep = d_equalityEngine.getRepresentative(term);
  if (rep != term) {
    alreadyNotified = 0;
    theoriesFind = d_alreadyNotifiedMap.find(rep);
    if (theoriesFind != d_alreadyNotifiedMap.end()) {
      alreadyNotified = (*theoriesFind).second;
    }
  }

  // For each theory that is newly notified
  for (TheoryId theory = THEORY_FIRST; theory != THEORY_LAST; ++ theory) {
    if (Theory::setContains(theory, newlyNotified)) {

      Debug("shared-terms-database") << "SharedTermsDatabase::markNotified: processing theory " << theory << endl;

      if (Theory::setContains(theory, alreadyNotified)) {
        // rep represents this theory already, need to assert that term = rep
        Assert(rep != term);
        assertEq(rep.eqNode(term), theory);
      }
      else {
        // Get the list of terms representing theories for this EC
        TermToNotifyList::iterator it = d_termToNotifyList.find(rep);
        if (it == d_termToNotifyList.end()) {
          // No need to do anything - no list associated with this EC
          Assert(term == rep);
        }
        else {
          NotifyList* pnl = (*it).second;
          Assert(pnl != NULL);

          // Check if this theory is already represented
          NotifyList::iterator nit = pnl->find(theory);
          if (nit != pnl->end()) {
            // Already have a representative for this theory, assert term equal to it
            assertEq((*nit).second.eqNode(term), theory);
          }
          else {
            // if term == rep, no need to do anything, as term will represent the theory via alreadyNotifiedMap
            if (term != rep) {
              // No term in this EC represents this theory, so add term as a new representative
              Debug("shared-terms-database") << "SharedTermsDatabase::markNotified: adding " << term << " to representative " << rep << " for theory " << theory << endl;
              (*pnl)[theory] = term;
            }
          }
        }
      }
    }
  }
}


bool SharedTermsDatabase::areEqual(TNode a, TNode b) {
  return d_equalityEngine.areEqual(a,b);
}


bool SharedTermsDatabase::areDisequal(TNode a, TNode b) {
  return d_equalityEngine.areDisequal(a,b);
}

void SharedTermsDatabase::processSharedLiteral(TNode literal, TNode reason)
{
  bool negated = literal.getKind() == kind::NOT;
  TNode atom = negated ? literal[0] : literal;
  if (negated) {
    Assert(!d_equalityEngine.areDisequal(atom[0], atom[1]));
    d_equalityEngine.assertEquality(atom, false, reason);
    //    !!! need to send this out
  }
  else {
    Assert(!d_equalityEngine.areEqual(atom[0], atom[1]));
    d_equalityEngine.assertEquality(atom, true, reason);
  }
}

static Node mkAnd(const std::vector<TNode>& conjunctions) {
  Assert(conjunctions.size() > 0);

  std::set<TNode> all;
  all.insert(conjunctions.begin(), conjunctions.end());

  if (all.size() == 1) {
    // All the same, or just one
    return conjunctions[0];
  }

  NodeBuilder<> conjunction(kind::AND);
  std::set<TNode>::const_iterator it = all.begin();
  std::set<TNode>::const_iterator it_end = all.end();
  while (it != it_end) {
    conjunction << *it;
    ++ it;
  }

  return conjunction;
}/* mkAnd() */


Node SharedTermsDatabase::explain(TNode literal)
{
  std::vector<TNode> assumptions;
  if (literal.getKind() == kind::NOT) {
    Assert(literal[0].getKind() == kind::EQUAL);
    d_equalityEngine.explainEquality(literal[0][0], literal[0][1], false, assumptions);
  } else {
    Assert(literal.getKind() == kind::EQUAL);
    d_equalityEngine.explainEquality(literal[0], literal[1], true, assumptions);
  }
  return mkAnd(assumptions);
}

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
#include "theory/uf/equality_engine_impl.h"

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
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst<bool>(true);
  d_false = nm->mkConst<bool>(false);
  d_equalityEngine.addTerm(d_true);
  d_equalityEngine.addTerm(d_false);
  d_equalityEngine.addTriggerEquality(d_true, d_false, d_false);
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
             ((nit = pnlRight->end()) != pnlRight->end())) {
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

    // Normalize the equality
    Node equality = left.eqNode(right);
    Node normalized = Rewriter::rewriteEquality(currentTheory, equality);
    if (normalized.getKind() != kind::CONST_BOOLEAN || !normalized.getConst<bool>()) {
      // Notify client
      d_sharedNotify.notify(normalized, equality, currentTheory);
    }
  }

}
  

void SharedTermsDatabase::markNotified(TNode term, Theory::Set theories) {
  Theory::Set alreadyNotified = d_alreadyNotifiedMap[term];
  Theory::Set newlyNotified = Theory::setDifference(theories, alreadyNotified);
  if (newlyNotified != 0) {
    TNode rep = d_equalityEngine.getRepresentative(term);
    if (rep != term) {
      TermToNotifyList::iterator it = d_termToNotifyList.find(rep);
      Assert(it != d_termToNotifyList.end());
      NotifyList* pnl = (*it).second;
      for (TheoryId theory = THEORY_FIRST; theory != THEORY_LAST; ++ theory) {
        if (Theory::setContains(theory, newlyNotified) &&
            pnl->find(theory) == pnl->end()) {
          (*pnl)[theory] = term;
        }
      }
    }
  }
  d_alreadyNotifiedMap[term] = Theory::setUnion(newlyNotified, alreadyNotified);
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
    d_equalityEngine.addDisequality(atom[0], atom[1], reason);
    //    !!! need to send this out
  }
  else {
    Assert(!d_equalityEngine.areEqual(atom[0], atom[1]));
    d_equalityEngine.addEquality(atom[0], atom[1], reason);
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
  explain(literal, assumptions);
  return mkAnd(assumptions);
}


void SharedTermsDatabase::explain(TNode literal, std::vector<TNode>& assumptions) {
  TNode lhs, rhs;
  switch (literal.getKind()) {
    case kind::EQUAL:
      lhs = literal[0];
      rhs = literal[1];
      break;
    case kind::NOT:
      if (literal[0].getKind() == kind::EQUAL) {
        // Disequalities
        d_equalityEngine.explainDisequality(literal[0][0], literal[0][1], assumptions);
        return;
      }
    case kind::CONST_BOOLEAN:
      // we get to explain true = false, since we set false to be the trigger of this
      lhs = d_true;
      rhs = d_false;
      break;
    default:
      Unreachable();
  }
  d_equalityEngine.explainEquality(lhs, rhs, assumptions);
}

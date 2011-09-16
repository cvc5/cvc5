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

using namespace CVC4;
using namespace CVC4::theory;

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

void SharedTermsDatabase::markNotified(TNode term, Theory::Set theories) {
  d_alreadyNotifiedMap[term] = Theory::setUnion(theories, d_alreadyNotifiedMap[term]);
}


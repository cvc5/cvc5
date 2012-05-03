/*********************                                                        */
/*! \file term_registration_visitor.h
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: 
 ** Minor contributors (to current version):
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **/

#include "theory/term_registration_visitor.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace theory;

std::string PreRegisterVisitor::toString() const {
  std::stringstream ss;
  TNodeToTheorySetMap::const_iterator it = d_visited.begin();
  for (; it != d_visited.end(); ++ it) {
    ss << (*it).first << ": " << Theory::setToString((*it).second) << std::endl;
  }
  return ss.str();
}

bool PreRegisterVisitor::alreadyVisited(TNode current, TNode parent) {

  Debug("register::internal") << "PreRegisterVisitor::alreadyVisited(" << current << "," << parent << ") => ";

  TNodeToTheorySetMap::iterator find = d_visited.find(current);

  // If node is not visited at all, just return false
  if (find == d_visited.end()) {
    Debug("register::internal") << "1:false" << std::endl;
    return false;
  }

  Theory::Set theories;

  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  // Remember the theories interested in this term
  d_theories[parent] = theories = Theory::setInsert(currentTheoryId, d_theories[parent]);
  // Check if there are multiple of those
  d_multipleTheories = d_multipleTheories || Theory::setRemove(parentTheoryId, theories);

  theories = (*find).second;
  if (Theory::setContains(currentTheoryId, theories)) {
    // The current theory has already visited it, so now it depends on the parent
    Debug("register::internal") << (Theory::setContains(parentTheoryId, theories) ? "2:true" : "2:false") << std::endl;
    return Theory::setContains(parentTheoryId, theories);
  } else {
    // If the current theory is not registered, it still needs to be visited
    Debug("register::internal") << "3:false" << std::endl;
    return false;
  }
}

void PreRegisterVisitor::visit(TNode current, TNode parent) {

  Theory::Set theories;

  Debug("register") << "PreRegisterVisitor::visit(" << current << "," << parent << ")" << std::endl;
  Debug("register::internal") << toString() << std::endl;

  // Get the theories of the terms
  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  // Remember the theories interested in this term
  d_theories[parent] = theories = Theory::setInsert(currentTheoryId, d_theories[parent]);
  // If there are theories other than the parent itself, we are in multi-theory case
  d_multipleTheories = d_multipleTheories || Theory::setRemove(parentTheoryId, theories);

  theories = d_visited[current];
  Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): previously registered with " << Theory::setToString(theories) << std::endl;
  if (!Theory::setContains(currentTheoryId, theories)) {
    d_visited[current] = theories = Theory::setInsert(currentTheoryId, theories);
    d_engine->theoryOf(currentTheoryId)->preRegisterTerm(current);
    Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << currentTheoryId << std::endl;
  }
  if (!Theory::setContains(parentTheoryId, theories)) {
    d_visited[current] = theories = Theory::setInsert(parentTheoryId, theories);
    d_engine->theoryOf(parentTheoryId)->preRegisterTerm(current);
    Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
  }
  Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): now registered with " << Theory::setToString(theories) << std::endl;

  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

void PreRegisterVisitor::start(TNode node) {
  d_multipleTheories = false;
}

bool PreRegisterVisitor::done(TNode node) {
  return d_multipleTheories;
}

std::string SharedTermsVisitor::toString() const {
  std::stringstream ss;
  TNodeVisitedMap::const_iterator it = d_visited.begin();
  for (; it != d_visited.end(); ++ it) {
    ss << (*it).first << ": " << Theory::setToString((*it).second) << std::endl;
  }
  return ss.str();
}

bool SharedTermsVisitor::alreadyVisited(TNode current, TNode parent) const {

  Debug("register::internal") << "SharedTermsVisitor::alreadyVisited(" << current << "," << parent << ") => ";

  TNodeVisitedMap::const_iterator find = d_visited.find(current);

  // If node is not visited at all, just return false
  if (find == d_visited.end()) {
    Debug("register::internal") << "1:false" << std::endl;
    return false;
  }

  Theory::Set theories = (*find).second;

  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  if (Theory::setContains(currentTheoryId, theories)) {
    // The current theory has already visited it, so now it depends on the parent
    Debug("register::internal") << (Theory::setContains(parentTheoryId, theories) ? "2:true" : "2:false") << std::endl;
    return Theory::setContains(parentTheoryId, theories);
  } else {
    // If the current theory is not registered, it still needs to be visited
    Debug("register::internal") << "2:false" << std::endl;
    return false;
  }
}

void SharedTermsVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "SharedTermsVisitor::visit(" << current << "," << parent << ")" << std::endl;
  Debug("register::internal") << toString() << std::endl;

  // Get the theories of the terms
  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  Theory::Set theories = d_visited[current];
  unsigned theoriesCount = theories == 0 ? 0 : 1;
  Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): previously registered with " << Theory::setToString(theories) << std::endl;
  if (!Theory::setContains(currentTheoryId, theories)) {
    d_visited[current] = theories = Theory::setInsert(currentTheoryId, theories);
    theoriesCount ++;
    Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): adding " << currentTheoryId << std::endl;
  }
  if (!Theory::setContains(parentTheoryId, theories)) {
    d_visited[current] = theories = Theory::setInsert(parentTheoryId, theories);
    theoriesCount ++;
    Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
  }
  Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): now registered with " << Theory::setToString(theories) << std::endl;

  // If there is more than two theories and a new one has been added notify the shared terms database
  if (theoriesCount > 1) {
    d_sharedTerms.addSharedTerm(d_atom, current, theories);
  }

  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

void SharedTermsVisitor::start(TNode node) {
  clear();
  d_atom = node;
}

void SharedTermsVisitor::done(TNode node) {
  clear();
}

void SharedTermsVisitor::clear() {
  d_atom = TNode();
  d_visited.clear();
}

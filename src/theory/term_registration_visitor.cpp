/*********************                                                        */
/*! \file term_registration_visitor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/term_registration_visitor.h"

#include "options/quantifiers_options.h"
#include "theory/theory_engine.h"

using namespace CVC4::theory;

namespace CVC4 {

std::string PreRegisterVisitor::toString() const {
  std::stringstream ss;
  TNodeToTheorySetMap::const_iterator it = d_visited.begin();
  for (; it != d_visited.end(); ++ it) {
    ss << (*it).first << ": " << TheoryIdSetUtil::setToString((*it).second)
       << std::endl;
  }
  return ss.str();
}

/**
 * Return true if we should visit current from parent, given that the
 * set of theories in visitedTheories has already visited current. This method
 * is used by both visitors below.
 */
bool shouldVisit(TheoryIdSet visitedTheories, TNode current, TNode parent)
{
  TheoryId currentTheoryId = Theory::theoryOf(current);
  if (!TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    // current theory not visited, return true
    return true;
  }

  if (current == parent)
  {
    // top-level and current visited, return false
    return false;
  }

  // The current theory has already visited it, so now it depends on the parent
  // and the type
  TheoryId parentTheoryId = Theory::theoryOf(parent);
  if (!TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
  {
    // parent theory not visited, return true
    return true;
  }

  // do we need to consider the type?
  TypeNode type = current.getType();
  if (currentTheoryId == parentTheoryId && !type.isInterpretedFinite())
  {
    // current and parent are the same theory, and we are infinite, return false
    return false;
  }
  TheoryId typeTheoryId = Theory::theoryOf(type);
  return !TheoryIdSetUtil::setContains(typeTheoryId, visitedTheories);
}

bool PreRegisterVisitor::alreadyVisited(TNode current, TNode parent) {

  Debug("register::internal") << "PreRegisterVisitor::alreadyVisited(" << current << "," << parent << ")" << std::endl;

  if ((parent.isClosure()
       || parent.getKind() == kind::SEP_STAR
       || parent.getKind() == kind::SEP_WAND
       || (parent.getKind() == kind::SEP_LABEL && current.getType().isBoolean())
       // parent.getKind() == kind::CARDINALITY_CONSTRAINT
       )
      && current != parent)
  {
    Debug("register::internal") << "quantifier:true" << std::endl;
    return true;
  }
  
  // Get the theories that have already visited this node
  TNodeToTheorySetMap::iterator find = d_visited.find(current);
  if (find == d_visited.end()) {
    // not visited at all, return false
    return false;
  }

  TheoryIdSet visitedTheories = (*find).second;
  return !shouldVisit(visitedTheories, current, parent);
}

void PreRegisterVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "PreRegisterVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }

  // get the theories we already preregistered with
  TheoryIdSet visitedTheories = d_visited[current];

  // call the preregistration on current, parent or type theories and update
  // visitedTheories.
  preregister(d_engine, visitedTheories, current, parent);

  Debug("register::internal")
      << "PreRegisterVisitor::visit(" << current << "," << parent
      << "): now registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;
  // update the theories set for current
  d_visited[current] = visitedTheories;
  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

void PreRegisterVisitor::preregister(TheoryEngine* te,
                                     TheoryIdSet& visitedTheories,
                                     TNode current,
                                     TNode parent)
{
  // Preregister with the current theory, if necessary
  TheoryId currentTheoryId = Theory::theoryOf(current);
  if (!TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    visitedTheories =
        TheoryIdSetUtil::setInsert(currentTheoryId, visitedTheories);
    Theory* th = te->theoryOf(currentTheoryId);
    th->preRegisterTerm(current);
    Debug("register::internal")
        << "PreRegisterVisitor::visit(" << current << "," << parent
        << "): adding " << currentTheoryId << std::endl;
  }

  if (current != parent)
  {
    // preregister with parent theory, if necessary
    TheoryId parentTheoryId = Theory::theoryOf(parent);
    if (!TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
    {
      visitedTheories =
          TheoryIdSetUtil::setInsert(parentTheoryId, visitedTheories);
      Theory* th = te->theoryOf(parentTheoryId);
      th->preRegisterTerm(current);
      Debug("register::internal")
          << "PreRegisterVisitor::visit(" << current << "," << parent
          << "): adding " << parentTheoryId << std::endl;
    }

    // Should we use the theory of the type
    TypeNode type = current.getType();
    if (currentTheoryId != parentTheoryId || type.isInterpretedFinite())
    {
      TheoryId typeTheoryId = Theory::theoryOf(type);
      if (!TheoryIdSetUtil::setContains(typeTheoryId, visitedTheories))
      {
        visitedTheories =
            TheoryIdSetUtil::setInsert(typeTheoryId, visitedTheories);
        Theory* th = te->theoryOf(typeTheoryId);
        th->preRegisterTerm(current);
        Debug("register::internal")
            << "PreRegisterVisitor::visit(" << current << "," << parent
            << "): adding " << typeTheoryId << std::endl;
      }
    }
  }
}

void PreRegisterVisitor::start(TNode node) {}

std::string SharedTermsVisitor::toString() const {
  std::stringstream ss;
  TNodeVisitedMap::const_iterator it = d_visited.begin();
  for (; it != d_visited.end(); ++ it) {
    ss << (*it).first << ": " << TheoryIdSetUtil::setToString((*it).second)
       << std::endl;
  }
  return ss.str();
}

bool SharedTermsVisitor::alreadyVisited(TNode current, TNode parent) const {

  Debug("register::internal") << "SharedTermsVisitor::alreadyVisited(" << current << "," << parent << ")" << std::endl;

  if ((parent.isClosure()
       || parent.getKind() == kind::SEP_STAR
       || parent.getKind() == kind::SEP_WAND
       || (parent.getKind() == kind::SEP_LABEL && current.getType().isBoolean())
       // parent.getKind() == kind::CARDINALITY_CONSTRAINT
       )
      && current != parent)
  {
    Debug("register::internal") << "quantifier:true" << std::endl;
    return true;
  }
  TNodeVisitedMap::const_iterator find = d_visited.find(current);
  // If node is not visited at all, just return false
  if (find == d_visited.end()) {
    Debug("register::internal") << "1:false" << std::endl;
    return false;
  }

  TheoryIdSet visitedTheories = (*find).second;
  return !shouldVisit(visitedTheories, current, parent);
}

void SharedTermsVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "SharedTermsVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }
  TheoryIdSet visitedTheories = d_visited[current];

  // preregister the term with the current, parent or type theories, as needed
  PreRegisterVisitor::preregister(d_engine, visitedTheories, current, parent);

  // Record the new theories that we visited
  d_visited[current] = visitedTheories;

  // If there is more than two theories and a new one has been added notify the shared terms database
  TheoryId currentTheoryId = Theory::theoryOf(current);  // TODO: remove
  if (TheoryIdSetUtil::setDifference(
          visitedTheories, TheoryIdSetUtil::setInsert(currentTheoryId)))
  {
    d_sharedTerms.addSharedTerm(d_atom, current, visitedTheories);
  }

  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

void SharedTermsVisitor::start(TNode node) {
  d_visited.clear();
  d_atom = node;
}

void SharedTermsVisitor::done(TNode node) {
  clear();
}

void SharedTermsVisitor::clear() {
  d_atom = TNode();
  d_visited.clear();
}

}  // namespace CVC4

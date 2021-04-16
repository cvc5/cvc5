/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "theory/term_registration_visitor.h"

#include "base/configuration.h"
#include "options/quantifiers_options.h"
#include "smt/logic_exception.h"
#include "theory/theory_engine.h"

using namespace cvc5::theory;

namespace cvc5 {

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
 * Return true if we already visited the term current with the given parent,
 * assuming that the set of theories in visitedTheories has already processed
 * current. This method is used by PreRegisterVisitor and SharedTermsVisitor
 * below.
 */
bool isAlreadyVisited(TheoryEngine* te,
                      TheoryIdSet visitedTheories,
                      TNode current,
                      TNode parent)
{
  TheoryId currentTheoryId = Theory::theoryOf(current);
  if (!TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    // current theory not visited, return false
    return false;
  }

  if (current == parent)
  {
    // top-level and current visited, return true
    return true;
  }

  // The current theory has already visited it, so now it depends on the parent
  // and the type
  TheoryId parentTheoryId = Theory::theoryOf(parent);
  if (!TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
  {
    // parent theory not visited, return false
    return false;
  }

  // do we need to consider the type?
  TypeNode type = current.getType();
  if (currentTheoryId == parentTheoryId && !te->isFiniteType(type))
  {
    // current and parent are the same theory, and we are infinite, return true
    return true;
  }
  TheoryId typeTheoryId = Theory::theoryOf(type);
  return TheoryIdSetUtil::setContains(typeTheoryId, visitedTheories);
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
  return isAlreadyVisited(d_engine, visitedTheories, current, parent);
}

void PreRegisterVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "PreRegisterVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }

  // get the theories we already preregistered with
  TheoryIdSet visitedTheories = d_visited[current];

  // call the preregistration on current, parent or type theories and update
  // visitedTheories. The set of preregistering theories coincides with
  // visitedTheories here.
  preRegister(d_engine, visitedTheories, current, parent, visitedTheories);

  Debug("register::internal")
      << "PreRegisterVisitor::visit(" << current << "," << parent
      << "): now registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;
  // update the theories set for current
  d_visited[current] = visitedTheories;
  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

void PreRegisterVisitor::preRegister(TheoryEngine* te,
                                     TheoryIdSet& visitedTheories,
                                     TNode current,
                                     TNode parent,
                                     TheoryIdSet preregTheories)
{
  // Preregister with the current theory, if necessary
  TheoryId currentTheoryId = Theory::theoryOf(current);
  preRegisterWithTheory(
      te, visitedTheories, currentTheoryId, current, parent, preregTheories);

  if (current != parent)
  {
    // preregister with parent theory, if necessary
    TheoryId parentTheoryId = Theory::theoryOf(parent);
    preRegisterWithTheory(
        te, visitedTheories, parentTheoryId, current, parent, preregTheories);

    // Note that if enclosed by different theories it's shared, for example,
    // in read(a, f(a)), f(a) should be shared with integers.
    TypeNode type = current.getType();
    if (currentTheoryId != parentTheoryId || te->isFiniteType(type))
    {
      // preregister with the type's theory, if necessary
      TheoryId typeTheoryId = Theory::theoryOf(type);
      preRegisterWithTheory(
          te, visitedTheories, typeTheoryId, current, parent, preregTheories);
    }
  }
}
void PreRegisterVisitor::preRegisterWithTheory(TheoryEngine* te,
                                               TheoryIdSet& visitedTheories,
                                               TheoryId id,
                                               TNode current,
                                               TNode parent,
                                               TheoryIdSet preregTheories)
{
  if (TheoryIdSetUtil::setContains(id, visitedTheories))
  {
    // already visited
    return;
  }
  visitedTheories = TheoryIdSetUtil::setInsert(id, visitedTheories);
  if (TheoryIdSetUtil::setContains(id, preregTheories))
  {
    // already pregregistered
    return;
  }
  if (Configuration::isAssertionBuild())
  {
    Debug("register::internal")
        << "PreRegisterVisitor::visit(" << current << "," << parent
        << "): adding " << id << std::endl;
    // This should never throw an exception, since theories should be
    // guaranteed to be initialized.
    // These checks don't work with finite model finding, because it
    // uses Rational constants to represent cardinality constraints,
    // even though arithmetic isn't actually involved.
    if (!options::finiteModelFind())
    {
      if (!te->isTheoryEnabled(id))
      {
        const LogicInfo& l = te->getLogicInfo();
        LogicInfo newLogicInfo = l.getUnlockedCopy();
        newLogicInfo.enableTheory(id);
        newLogicInfo.lock();
        std::stringstream ss;
        ss << "The logic was specified as " << l.getLogicString()
           << ", which doesn't include " << id
           << ", but found a term in that theory." << std::endl
           << "You might want to extend your logic to "
           << newLogicInfo.getLogicString() << std::endl;
        throw LogicException(ss.str());
      }
    }
  }
  // call the theory's preRegisterTerm method
  Theory* th = te->theoryOf(id);
  th->preRegisterTerm(current);
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
  return isAlreadyVisited(d_engine, visitedTheories, current, parent);
}

void SharedTermsVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "SharedTermsVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }
  TheoryIdSet visitedTheories = d_visited[current];
  TheoryIdSet preregTheories = d_preregistered[current];

  // preregister the term with the current, parent or type theories, as needed
  PreRegisterVisitor::preRegister(
      d_engine, visitedTheories, current, parent, preregTheories);

  // Record the new theories that we visited
  d_visited[current] = visitedTheories;

  // add visited theories to those who have preregistered
  d_preregistered[current] =
      TheoryIdSetUtil::setUnion(preregTheories, visitedTheories);

  // If there is more than two theories and a new one has been added notify the shared terms database
  TheoryId currentTheoryId = Theory::theoryOf(current);
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

}  // namespace cvc5

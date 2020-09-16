/*********************                                                        */
/*! \file term_registration_visitor.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/term_registration_visitor.h"

#include "options/quantifiers_options.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace theory;

std::string PreRegisterVisitor::toString() const {
  std::stringstream ss;
  TNodeToTheorySetMap::const_iterator it = d_visited.begin();
  for (; it != d_visited.end(); ++ it) {
    ss << (*it).first << ": " << TheoryIdSetUtil::setToString((*it).second)
       << std::endl;
  }
  return ss.str();
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

  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId = Theory::theoryOf(parent);

  d_theories = TheoryIdSetUtil::setInsert(currentTheoryId, d_theories);
  d_theories = TheoryIdSetUtil::setInsert(parentTheoryId, d_theories);

  // Should we use the theory of the type
  bool useType = false;
  TheoryId typeTheoryId = THEORY_LAST;

  if (current != parent) {
    if (currentTheoryId != parentTheoryId) {
      // If enclosed by different theories it's shared -- in read(a, f(a)) f(a) should be shared with integers
      TypeNode type = current.getType();
      useType = true;
      typeTheoryId = Theory::theoryOf(type);
    } else {
      TypeNode type = current.getType();
      typeTheoryId = Theory::theoryOf(type);
      if (typeTheoryId != currentTheoryId) {
        if (type.isInterpretedFinite()) {
          useType = true;
        }
      }
    }
  }
  
  // Get the theories that have already visited this node
  TNodeToTheorySetMap::iterator find = d_visited.find(current);
  if (find == d_visited.end()) {
    if (useType) {
      d_theories = TheoryIdSetUtil::setInsert(typeTheoryId, d_theories);
    }
    return false;
  }

  TheoryIdSet visitedTheories = (*find).second;
  if (TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    // The current theory has already visited it, so now it depends on the parent and the type
    if (TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
    {
      if (useType) {
        TheoryId typeTheoryId2 = Theory::theoryOf(current.getType());
        d_theories = TheoryIdSetUtil::setInsert(typeTheoryId2, d_theories);
        return TheoryIdSetUtil::setContains(typeTheoryId2, visitedTheories);
      } else {
        return true;
      }
    } else {
      return false;
    }
  } else {
    return false;
  }
}

void PreRegisterVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "PreRegisterVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }

  // Get the theories of the terms
  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  // Should we use the theory of the type
  bool useType = false;
  TheoryId typeTheoryId = THEORY_LAST;

  if (current != parent) {
    if (currentTheoryId != parentTheoryId) {
      // If enclosed by different theories it's shared -- in read(a, f(a)) f(a) should be shared with integers
      TypeNode type = current.getType();
      useType = true;
      typeTheoryId = Theory::theoryOf(type);
    } else {
      TypeNode type = current.getType();
      typeTheoryId = Theory::theoryOf(type);
      if (typeTheoryId != currentTheoryId) {
        if (type.isInterpretedFinite()) {
          useType = true;
        }
      }
    }
  }

  TheoryIdSet visitedTheories = d_visited[current];
  Debug("register::internal")
      << "PreRegisterVisitor::visit(" << current << "," << parent
      << "): previously registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;
  if (!TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    visitedTheories =
        TheoryIdSetUtil::setInsert(currentTheoryId, visitedTheories);
    d_visited[current] = visitedTheories;
    Theory* th = d_engine->theoryOf(currentTheoryId);
    th->preRegisterTerm(current);
    Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << currentTheoryId << std::endl;
  }
  if (!TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
  {
    visitedTheories =
        TheoryIdSetUtil::setInsert(parentTheoryId, visitedTheories);
    d_visited[current] = visitedTheories;
    Theory* th = d_engine->theoryOf(parentTheoryId);
    th->preRegisterTerm(current);
    Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
  }
  if (useType) {
    if (!TheoryIdSetUtil::setContains(typeTheoryId, visitedTheories))
    {
      visitedTheories =
          TheoryIdSetUtil::setInsert(typeTheoryId, visitedTheories);
      d_visited[current] = visitedTheories;
      Theory* th = d_engine->theoryOf(typeTheoryId);
      th->preRegisterTerm(current);
      Debug("register::internal") << "PreRegisterVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
    }
  }
  Debug("register::internal")
      << "PreRegisterVisitor::visit(" << current << "," << parent
      << "): now registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;

  Assert(d_visited.find(current) != d_visited.end());
  Assert(alreadyVisited(current, parent));
}

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

  TheoryIdSet theories = (*find).second;

  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  // Should we use the theory of the type
  bool useType = false;
  TheoryId typeTheoryId = THEORY_LAST;

  if (current != parent) {
    if (currentTheoryId != parentTheoryId) {
      // If enclosed by different theories it's shared -- in read(a, f(a)) f(a) should be shared with integers
      TypeNode type = current.getType();
      useType = true;
      typeTheoryId = Theory::theoryOf(type);
    } else {
      TypeNode type = current.getType();
      typeTheoryId = Theory::theoryOf(type);
      if (typeTheoryId != currentTheoryId) {
        if (type.isInterpretedFinite()) {
          useType = true;
        }
      }
    }
  }
  if (current != parent) {
    if (currentTheoryId != parentTheoryId) {
      // If enclosed by different theories it's shared -- in read(a, f(a)) f(a) should be shared with integers
      TypeNode type = current.getType();
      useType = true;
      typeTheoryId = Theory::theoryOf(type);
    } else {
      TypeNode type = current.getType();
      typeTheoryId = Theory::theoryOf(type);
      if (typeTheoryId != currentTheoryId) {
        if (type.isInterpretedFinite()) {
          useType = true;
        }
      }
    }
  }

  if (TheoryIdSetUtil::setContains(currentTheoryId, theories))
  {
    if (TheoryIdSetUtil::setContains(parentTheoryId, theories))
    {
      if (useType)
      {
        return TheoryIdSetUtil::setContains(typeTheoryId, theories);
      }
      else
      {
        return true;
      }
    }
    else
    {
      return false;
    }
  } else {
    return false;
  }
}

void SharedTermsVisitor::visit(TNode current, TNode parent) {

  Debug("register") << "SharedTermsVisitor::visit(" << current << "," << parent << ")" << std::endl;
  if (Debug.isOn("register::internal")) {
    Debug("register::internal") << toString() << std::endl;
  }

  // Get the theories of the terms
  TheoryId currentTheoryId = Theory::theoryOf(current);
  TheoryId parentTheoryId  = Theory::theoryOf(parent);

  // Should we use the theory of the type
  bool useType = false;
  TheoryId typeTheoryId = THEORY_LAST;

  if (current != parent) {
    if (currentTheoryId != parentTheoryId) {
      // If enclosed by different theories it's shared -- in read(a, f(a)) f(a) should be shared with integers
      TypeNode type = current.getType();
      useType = true;
      typeTheoryId = Theory::theoryOf(type);
    } else {
      TypeNode type = current.getType();
      typeTheoryId = Theory::theoryOf(type);
      if (typeTheoryId != currentTheoryId) {
        if (type.isInterpretedFinite()) {
          useType = true;
        }
      }
    }
  }

  TheoryIdSet visitedTheories = d_visited[current];
  Debug("register::internal")
      << "SharedTermsVisitor::visit(" << current << "," << parent
      << "): previously registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;
  if (!TheoryIdSetUtil::setContains(currentTheoryId, visitedTheories))
  {
    visitedTheories =
        TheoryIdSetUtil::setInsert(currentTheoryId, visitedTheories);
    Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): adding " << currentTheoryId << std::endl;
  }
  if (!TheoryIdSetUtil::setContains(parentTheoryId, visitedTheories))
  {
    visitedTheories =
        TheoryIdSetUtil::setInsert(parentTheoryId, visitedTheories);
    Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): adding " << parentTheoryId << std::endl;
  }
  if (useType) {
    if (!TheoryIdSetUtil::setContains(typeTheoryId, visitedTheories))
    {
      visitedTheories =
          TheoryIdSetUtil::setInsert(typeTheoryId, visitedTheories);
      Debug("register::internal") << "SharedTermsVisitor::visit(" << current << "," << parent << "): adding " << typeTheoryId << std::endl;
    }
  }
  Debug("register::internal")
      << "SharedTermsVisitor::visit(" << current << "," << parent
      << "): now registered with "
      << TheoryIdSetUtil::setToString(visitedTheories) << std::endl;

  // Record the new theories that we visited
  d_visited[current] = visitedTheories;

  // If there is more than two theories and a new one has been added notify the shared terms database
  if (TheoryIdSetUtil::setDifference(
          visitedTheories, TheoryIdSetUtil::setInsert(currentTheoryId)))
  {
    d_sharedTerms.addSharedTerm(d_atom, current, visitedTheories);
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

/*********************                                                        */
/*! \file valuation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** Implementation of Valuation class.
 **/

#include "theory/valuation.h"

#include "expr/node.h"
#include "options/theory_options.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {

std::ostream& operator<<(std::ostream& os, EqualityStatus s)
{
  switch (s)
  {
    case EQUALITY_TRUE_AND_PROPAGATED:
      os << "EQUALITY_TRUE_AND_PROPAGATED";
      break;
    case EQUALITY_FALSE_AND_PROPAGATED:
      os << "EQUALITY_FALSE_AND_PROPAGATED";
      break;
    case EQUALITY_TRUE: os << "EQUALITY_TRUE"; break;
    case EQUALITY_FALSE: os << "EQUALITY_FALSE"; break;
    case EQUALITY_TRUE_IN_MODEL: os << "EQUALITY_TRUE_IN_MODEL"; break;
    case EQUALITY_FALSE_IN_MODEL: os << "EQUALITY_FALSE_IN_MODEL"; break;
    case EQUALITY_UNKNOWN: os << "EQUALITY_UNKNOWN"; break;
    default: Unhandled(); break;
  }
  return os;
}

bool equalityStatusCompatible(EqualityStatus s1, EqualityStatus s2) {
  switch (s1) {
  case EQUALITY_TRUE:
  case EQUALITY_TRUE_IN_MODEL:
  case EQUALITY_TRUE_AND_PROPAGATED:
    switch (s2) {
    case EQUALITY_TRUE:
    case EQUALITY_TRUE_IN_MODEL:
    case EQUALITY_TRUE_AND_PROPAGATED:
      return true;
    default:
      return false;
    }
    break;
  case EQUALITY_FALSE:
  case EQUALITY_FALSE_IN_MODEL:
  case EQUALITY_FALSE_AND_PROPAGATED:
    switch (s2) {
    case EQUALITY_FALSE:
    case EQUALITY_FALSE_IN_MODEL:
    case EQUALITY_FALSE_AND_PROPAGATED:
      return true;
    default:
      return false;
    }
    break;
  default:
    return false;
  }
}

bool Valuation::isSatLiteral(TNode n) const {
  Assert(d_engine != nullptr);
  return d_engine->getPropEngine()->isSatLiteral(n);
}

Node Valuation::getSatValue(TNode n) const {
  Assert(d_engine != nullptr);
  if(n.getKind() == kind::NOT) {
    Node atomRes = d_engine->getPropEngine()->getValue(n[0]);
    if(atomRes.getKind() == kind::CONST_BOOLEAN) {
      return NodeManager::currentNM()->mkConst(!atomRes.getConst<bool>());
    } else {
      Assert(atomRes.isNull());
      return atomRes;
    }
  } else {
    return d_engine->getPropEngine()->getValue(n);
  }
}

bool Valuation::hasSatValue(TNode n, bool& value) const {
  Assert(d_engine != nullptr);
  if (d_engine->getPropEngine()->isSatLiteral(n)) {
    return d_engine->getPropEngine()->hasValue(n, value);
  } else {
    return false;
  }
}

EqualityStatus Valuation::getEqualityStatus(TNode a, TNode b) {
  Assert(d_engine != nullptr);
  return d_engine->getEqualityStatus(a, b);
}

Node Valuation::getModelValue(TNode var) {
  Assert(d_engine != nullptr);
  return d_engine->getModelValue(var);
}

TheoryModel* Valuation::getModel() {
  if (d_engine == nullptr)
  {
    // no theory engine, thus we don't have a model object
    return nullptr;
  }
  return d_engine->getModel();
}

void Valuation::setUnevaluatedKind(Kind k)
{
  TheoryModel* m = getModel();
  if (m != nullptr)
  {
    m->setUnevaluatedKind(k);
  }
  // If no model is available, this command has no effect. This is the case
  // when e.g. calling Theory::finishInit for theories that are using a
  // Valuation with no model.
}

void Valuation::setSemiEvaluatedKind(Kind k)
{
  TheoryModel* m = getModel();
  if (m != nullptr)
  {
    m->setSemiEvaluatedKind(k);
  }
}

void Valuation::setIrrelevantKind(Kind k)
{
  TheoryModel* m = getModel();
  if (m != nullptr)
  {
    m->setIrrelevantKind(k);
  }
}

Node Valuation::ensureLiteral(TNode n) {
  Assert(d_engine != nullptr);
  return d_engine->ensureLiteral(n);
}

bool Valuation::isDecision(Node lit) const {
  Assert(d_engine != nullptr);
  return d_engine->getPropEngine()->isDecision(lit);
}

unsigned Valuation::getAssertionLevel() const{
  Assert(d_engine != nullptr);
  return d_engine->getPropEngine()->getAssertionLevel();
}

std::pair<bool, Node> Valuation::entailmentCheck(options::TheoryOfMode mode,
                                                 TNode lit)
{
  Assert(d_engine != nullptr);
  return d_engine->entailmentCheck(mode, lit);
}

bool Valuation::needCheck() const{
  Assert(d_engine != nullptr);
  return d_engine->needCheck();
}

bool Valuation::isRelevant(Node lit) const { return d_engine->isRelevant(lit); }

}/* CVC4::theory namespace */
}/* CVC4 namespace */

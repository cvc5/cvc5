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
  return d_engine->getPropEngine()->isSatLiteral(n);
}

Node Valuation::getSatValue(TNode n) const {
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
  if (d_engine->getPropEngine()->isSatLiteral(n)) {
    return d_engine->getPropEngine()->hasValue(n, value);
  } else {
    return false;
  }
}

EqualityStatus Valuation::getEqualityStatus(TNode a, TNode b) {
  return d_engine->getEqualityStatus(a, b);
}

Node Valuation::getModelValue(TNode var) {
  return d_engine->getModelValue(var);
}

TheoryModel* Valuation::getModel() {
  return d_engine->getModel();
}

Node Valuation::ensureLiteral(TNode n) {
  return d_engine->ensureLiteral(n);
}

bool Valuation::isDecision(Node lit) const {
  return d_engine->getPropEngine()->isDecision(lit);
}

unsigned Valuation::getAssertionLevel() const{
  return d_engine->getPropEngine()->getAssertionLevel();
}

std::pair<bool, Node> Valuation::entailmentCheck(options::TheoryOfMode mode,
                                                 TNode lit)
{
  return d_engine->entailmentCheck(mode, lit);
}

bool Valuation::needCheck() const{
  return d_engine->needCheck();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

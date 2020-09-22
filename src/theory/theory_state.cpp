/*********************                                                        */
/*! \file theory_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A theory state for Theory
 **/

#include "theory/theory_state.h"

#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

TheoryState::TheoryState(context::Context* c,
                         context::UserContext* u,
                         Valuation val)
    : d_context(c),
      d_ucontext(u),
      d_valuation(val),
      d_ee(nullptr),
      d_conflict(c, false)
{
}

void TheoryState::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

context::Context* TheoryState::getSatContext() const { return d_context; }

context::UserContext* TheoryState::getUserContext() const { return d_ucontext; }

bool TheoryState::hasTerm(TNode a) const
{
  Assert(d_ee != nullptr);
  return d_ee->hasTerm(a);
}

TNode TheoryState::getRepresentative(TNode t) const
{
  Assert(d_ee != nullptr);
  if (d_ee->hasTerm(t))
  {
    return d_ee->getRepresentative(t);
  }
  return t;
}

bool TheoryState::areEqual(TNode a, TNode b) const
{
  Assert(d_ee != nullptr);
  if (a == b)
  {
    return true;
  }
  else if (hasTerm(a) && hasTerm(b))
  {
    return d_ee->areEqual(a, b);
  }
  return false;
}

bool TheoryState::areDisequal(TNode a, TNode b) const
{
  Assert(d_ee != nullptr);
  if (a == b)
  {
    return false;
  }

  bool isConst = true;
  bool hasTerms = true;
  if (hasTerm(a))
  {
    a = d_ee->getRepresentative(a);
    isConst = a.isConst();
  }
  else if (!a.isConst())
  {
    // if not constant and not a term in the ee, it cannot be disequal
    return false;
  }
  else
  {
    hasTerms = false;
  }

  if (hasTerm(b))
  {
    b = d_ee->getRepresentative(b);
    isConst = isConst && b.isConst();
  }
  else if (!b.isConst())
  {
    // same as above, it cannot be disequal
    return false;
  }
  else
  {
    hasTerms = false;
  }

  if (isConst)
  {
    // distinct constants are disequal
    return a != b;
  }
  else if (!hasTerms)
  {
    return false;
  }
  // otherwise there may be an explicit disequality in the equality engine
  return d_ee->areDisequal(a, b, false);
}

eq::EqualityEngine* TheoryState::getEqualityEngine() const { return d_ee; }

void TheoryState::notifyInConflict() { d_conflict = true; }

bool TheoryState::isInConflict() const { return d_conflict; }

bool TheoryState::isSatLiteral(TNode lit) const
{
  return d_valuation.isSatLiteral(lit);
}

TheoryModel* TheoryState::getModel() { return d_valuation.getModel(); }

bool TheoryState::hasSatValue(TNode n, bool& value) const
{
  return d_valuation.hasSatValue(n, value);
}

}  // namespace theory
}  // namespace CVC4

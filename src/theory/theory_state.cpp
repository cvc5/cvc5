/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A theory state for Theory.
 */

#include "theory/theory_state.h"

#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {

TheoryState::TheoryState(Env& env, Valuation val)
    : EnvObj(env), d_valuation(val), d_ee(nullptr), d_conflict(context(), false)
{
}

void TheoryState::setEqualityEngine(eq::EqualityEngine* ee) { d_ee = ee; }

bool TheoryState::hasTerm(TNode t) const
{
  Assert(d_ee != nullptr);
  return d_ee->hasTerm(t);
}

void TheoryState::addTerm(TNode t)
{
  Assert(d_ee != nullptr);
  d_ee->addTerm(t);
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

void TheoryState::getEquivalenceClass(Node a, std::vector<Node>& eqc) const
{
  if (d_ee->hasTerm(a))
  {
    Node rep = d_ee->getRepresentative(a);
    eq::EqClassIterator eqc_iter(rep, d_ee);
    while (!eqc_iter.isFinished())
    {
      eqc.push_back(*eqc_iter);
      eqc_iter++;
    }
  }
  else
  {
    eqc.push_back(a);
  }
  // a should be in its equivalence class
  Assert(std::find(eqc.begin(), eqc.end(), a) != eqc.end());
}

void TheoryState::addEqualityEngineTriggerPredicate(TNode pred)
{
  Assert(d_ee != nullptr);
  Assert(pred.getType().isBoolean());
  // if we don't already have a sat value
  if (!d_valuation.hasSatValue(pred))
  {
    // Get triggered for both equal and dis-equal
    d_ee->addTriggerPredicate(pred);
  }
  else
  {
    // otherwise we just add the term
    d_ee->addTerm(pred);
  }
}

eq::EqualityEngine* TheoryState::getEqualityEngine() const { return d_ee; }

void TheoryState::notifyInConflict() { d_conflict = true; }

bool TheoryState::isInConflict() const { return d_conflict; }

bool TheoryState::isSatLiteral(TNode lit) const
{
  return d_valuation.isSatLiteral(lit);
}

TheoryModel* TheoryState::getModel() { return d_valuation.getModel(); }

SortInference* TheoryState::getSortInference()
{
  return d_valuation.getSortInference();
}

bool TheoryState::hasSatValue(TNode n, bool& value) const
{
  return d_valuation.hasSatValue(n, value);
}

context::CDList<Assertion>::const_iterator TheoryState::factsBegin(TheoryId tid)
{
  return d_valuation.factsBegin(tid);
}
context::CDList<Assertion>::const_iterator TheoryState::factsEnd(TheoryId tid)
{
  return d_valuation.factsEnd(tid);
}

Valuation& TheoryState::getValuation() { return d_valuation; }

}  // namespace theory
}  // namespace cvc5::internal

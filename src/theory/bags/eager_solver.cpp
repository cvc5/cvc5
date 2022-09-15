/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eager solver.
 */

#include "theory/bags/eager_solver.h"

#include "options/bags_options.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

EagerSolver::EagerSolver(Env& env, SolverState& state, TermRegistry& treg)
    : EnvObj(env), d_state(state), d_treg(treg), d_aent(env.getRewriter())
{
}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  Kind k = t.getKind();
  NodeManager* nm = NodeManager::currentNM();
  Node zero = nm->mkConstInt(Rational(0));
  if (t.getType().isInteger())
  {
    EqcInfo* ei = d_state.getOrMakeEqcInfo(t, true);
    if (t.isConst())
    {
      // the constant is its bounds
      ei->addBoundConst(t, t, true);
      ei->addBoundConst(t, t, false);
    }
    if (k == BAG_COUNT)
    {
      // initial lower bound is zero, and upper bound is null (i.e., infinity)
      ei->addBoundConst(t, nm->mkConstInt(Rational(0)), true);
      Node bag = t[1];
      Kind bagKind = bag.getKind();
      switch (bagKind)
      {
        case BAG_EMPTY:
        {  // the constant is its bounds
          ei->addBoundConst(t, zero, true);
          ei->addBoundConst(t, zero, false);
          break;
        }
        case BAG_MAKE:
        {
          if (bag[1].isConst())
          {
            // (bag x c) implies c is both the lower and the upper bound
            ei->addBoundConst(t, bag[1], true);
            ei->addBoundConst(t, bag[1], false);
          }
          break;
        }

        default: break;
      }
    }
    Trace("bags-notify") << *ei << std::endl;
  }
}

void EagerSolver::eqNotifyMerge(EqcInfo* e1, TNode t1, EqcInfo* e2, TNode t2)
{
  Assert(e1 != nullptr);
  Assert(e2 != nullptr);
  if (t1.getType().isInteger())
  {
    e1->addBoundConst(t1, e2->d_firstBound, true);
    e1->addBoundConst(t1, e2->d_secondBound, false);
    e2->addBoundConst(t2, e1->d_firstBound, true);
    e2->addBoundConst(t2, e1->d_secondBound, false);
    propagateBounds(t1);
    propagateBounds(t2);

    Trace("bags-notify") << *e1 << std::endl;
    Trace("bags-notify") << *e2 << std::endl;
  }
}

void EagerSolver::propagateBounds(Node t1)
{
  if (t1.getKind() == BAG_COUNT)
  {
    Node bag = t1[1];
    Node bagRep = d_state.getRepresentative(bag);
    eq::EqClassIterator it =
        eq::EqClassIterator(bagRep, d_state.getEqualityEngine());
    while (!it.isFinished())
    {
      Node n = (*it);
      Kind k = n.getKind();
      switch (k)
      {
        case kind::BAG_EMPTY: break;
        case kind::BAG_MAKE: break;
        case kind::BAG_UNION_DISJOINT:
        {
          Trace("bags-notify") << "UNION_DISJOINT: " << n << std::endl;
          break;
        }
        case kind::BAG_UNION_MAX: break;
        case kind::BAG_INTER_MIN: break;
        case kind::BAG_DIFFERENCE_SUBTRACT: break;
        case kind::BAG_DIFFERENCE_REMOVE: break;
        case kind::BAG_DUPLICATE_REMOVAL: break;
        case kind::BAG_FILTER: break;
        case kind::BAG_MAP: break;
        case kind::TABLE_PRODUCT: break;
        case kind::TABLE_JOIN: break;
        case kind::TABLE_GROUP: break;
        default: break;
      }
      it++;
    }
  }
}

bool EagerSolver::checkForMergeConflict(Node a,
                                        Node b,
                                        EqcInfo* ea,
                                        EqcInfo* eb)
{
  Assert(eb != nullptr && ea != nullptr);
  Assert(a.getType() == b.getType())
      << "bad types for merge " << a << ", " << b;
  return false;
}

void EagerSolver::notifyFact(TNode atom,
                             bool polarity,
                             TNode fact,
                             bool isInternal)
{
}

bool EagerSolver::addArithmeticBound(EqcInfo* e, Node t, bool isLower)
{
  return false;
}

Node EagerSolver::getBoundForLength(Node t, bool isLower) const
{
  return Node::null();
}

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

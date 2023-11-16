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
#include "theory/bags/inference_manager.h"
#include "theory/uf/equality_engine_iterator.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace bags {

EagerSolver::EagerSolver(Env& env,
                         SolverState& s,
                         InferenceManager* im,
                         TermRegistry& treg)
    : EnvObj(env), d_state(s), d_im(im), d_ig(&s, im)
{
}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  if (t.getKind() == BAG_MAKE || t.getKind() == BAG_EMPTY)
  {
    EqcInfo* e = d_state.getOrMakeEqcInfo(t, true);
    e->d_representative = t;
  }
}

void EagerSolver::eqNotifyMerge(EqcInfo* e1, TNode t1, EqcInfo* e2, TNode t2)
{
  Assert(e1 != nullptr);
  Assert(e2 != nullptr);
  if (!d_state.isInConflict() && t1.getType().isBag())
  {
    Trace("bags-notify") << "EagerSolver::eqNotifyMerge::e1: " << *e1
                         << std::endl;
    Trace("bags-notify") << "EagerSolver::eqNotifyMerge::e2: " << *e2
                         << std::endl;
    Node n1 = e1->d_representative;
    Node n2 = e2->d_representative;
    if (n1.isNull() || n2.isNull())
    {
      return;
    }
    if (n1.getKind() == BAG_MAKE && n2.getKind() == BAG_MAKE)
    {
      if (!(n1[1].isConst() && n2[1].isConst()
            && n1[1].getConst<Rational>() > Rational(0)
            && n2[1].getConst<Rational>() > Rational(0)))
      {
        // only merge when the multiplicities are constants
        return;
      }
      InferInfo info = d_ig.mergeTwoBagMakeNodes(n1, n2);
      info.assertInternalFact();
    }
    else if ((n1.getKind() == BAG_MAKE && n2.getKind() == kind::BAG_EMPTY)
             || (n2.getKind() == BAG_MAKE && n1.getKind() == kind::BAG_EMPTY))
    {
      Node bagMake = n1.getKind() == BAG_MAKE ? n1 : n2;
      Node empty = n1.getKind() == BAG_EMPTY ? n1 : n2;
      if (bagMake[1].isConst() && bagMake[1].getConst<Rational>() > Rational(0))
      {
        // return a conflict when (as bag.empty (Bag E)) is merged with
        // (bag x c) where c > 0 is a constant
        Node equal = n1.eqNode(n2);
        Trace("bags-notify")
            << "EagerSolver::eqNotifyMerge:conflict " << equal << std::endl;
        d_im->conflict(equal, InferenceId::BAGS_EQ_CONFLICT);
      }
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

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

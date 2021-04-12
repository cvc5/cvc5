/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tianyi Liang, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eager solver.
 */

#include "theory/strings/eager_solver.h"

#include "theory/strings/theory_strings_utils.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

EagerSolver::EagerSolver(SolverState& state) : d_state(state) {}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  Kind k = t.getKind();
  if (k == STRING_LENGTH || k == STRING_TO_CODE)
  {
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    Node r = ee->getRepresentative(t[0]);
    EqcInfo* ei = d_state.getOrMakeEqcInfo(r);
    if (k == STRING_LENGTH)
    {
      ei->d_lengthTerm = t[0];
    }
    else
    {
      ei->d_codeTerm = t[0];
    }
  }
  else if (t.isConst())
  {
    if (t.getType().isStringLike())
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(t);
      ei->d_prefixC = t;
      ei->d_suffixC = t;
    }
  }
  else if (k == STRING_CONCAT)
  {
    addEndpointsToEqcInfo(t, t, t);
  }
}

void EagerSolver::eqNotifyMerge(TNode t1, TNode t2)
{
  EqcInfo* e2 = d_state.getOrMakeEqcInfo(t2, false);
  if (e2 == nullptr)
  {
    return;
  }
  Assert(t1.getType().isStringLike());
  EqcInfo* e1 = d_state.getOrMakeEqcInfo(t1);
  // add information from e2 to e1
  if (!e2->d_lengthTerm.get().isNull())
  {
    e1->d_lengthTerm.set(e2->d_lengthTerm);
  }
  if (!e2->d_codeTerm.get().isNull())
  {
    e1->d_codeTerm.set(e2->d_codeTerm);
  }
  if (!e2->d_prefixC.get().isNull())
  {
    d_state.setPendingPrefixConflictWhen(
        e1->addEndpointConst(e2->d_prefixC, Node::null(), false));
  }
  if (!e2->d_suffixC.get().isNull())
  {
    d_state.setPendingPrefixConflictWhen(
        e1->addEndpointConst(e2->d_suffixC, Node::null(), true));
  }
  if (e2->d_cardinalityLemK.get() > e1->d_cardinalityLemK.get())
  {
    e1->d_cardinalityLemK.set(e2->d_cardinalityLemK);
  }
  if (!e2->d_normalizedLength.get().isNull())
  {
    e1->d_normalizedLength.set(e2->d_normalizedLength);
  }
}

void EagerSolver::eqNotifyDisequal(TNode t1, TNode t2, TNode reason)
{
  if (t1.getType().isStringLike())
  {
    // store disequalities between strings, may need to check if their lengths
    // are equal/disequal
    d_state.addDisequality(t1, t2);
  }
}

void EagerSolver::addEndpointsToEqcInfo(Node t, Node concat, Node eqc)
{
  Assert(concat.getKind() == STRING_CONCAT
         || concat.getKind() == REGEXP_CONCAT);
  EqcInfo* ei = nullptr;
  // check each side
  for (unsigned r = 0; r < 2; r++)
  {
    unsigned index = r == 0 ? 0 : concat.getNumChildren() - 1;
    Node c = utils::getConstantComponent(concat[index]);
    if (!c.isNull())
    {
      if (ei == nullptr)
      {
        ei = d_state.getOrMakeEqcInfo(eqc);
      }
      Trace("strings-eager-pconf-debug")
          << "New term: " << concat << " for " << t << " with prefix " << c
          << " (" << (r == 1) << ")" << std::endl;
      d_state.setPendingPrefixConflictWhen(ei->addEndpointConst(t, c, r == 1));
    }
  }
}

void EagerSolver::notifyFact(TNode atom,
                             bool polarity,
                             TNode fact,
                             bool isInternal)
{
  if (atom.getKind() == STRING_IN_REGEXP)
  {
    if (polarity && atom[1].getKind() == REGEXP_CONCAT)
    {
      eq::EqualityEngine* ee = d_state.getEqualityEngine();
      Node eqc = ee->getRepresentative(atom[0]);
      addEndpointsToEqcInfo(atom, atom[1], eqc);
    }
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

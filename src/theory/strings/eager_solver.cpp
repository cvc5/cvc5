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
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace strings {

EagerSolver::EagerSolver(Env& env,
                         SolverState& state,
                         TermRegistry& treg,
                         ArithEntail& aent)
    : EnvObj(env), d_state(state), d_treg(treg), d_aent(aent)
{
}

EagerSolver::~EagerSolver() {}

void EagerSolver::eqNotifyNewClass(TNode t)
{
  Kind k = t.getKind();
  if (k == STRING_LENGTH)
  {
    // also assume it as upper/lower bound as applicable for the equivalence
    // class info of t.
    EqcInfo* eil = nullptr;
    for (size_t i = 0; i < 2; i++)
    {
      Node b = getBoundForLength(t, i == 0);
      if (b.isNull())
      {
        continue;
      }
      if (eil == nullptr)
      {
        eil = d_state.getOrMakeEqcInfo(t);
      }
      if (i == 0)
      {
        eil->d_firstBound = t;
      }
      else if (i == 1)
      {
        eil->d_secondBound = t;
      }
    }
  }
  else if (t.isConst())
  {
    TypeNode tn = t.getType();
    if (tn.isStringLike() || tn.isInteger())
    {
      EqcInfo* ei = d_state.getOrMakeEqcInfo(t);
      ei->d_firstBound = t;
      ei->d_secondBound = t;
    }
  }
  else if (k == STRING_CONCAT)
  {
    addEndpointsToEqcInfo(t, t, t);
  }
}

void EagerSolver::eqNotifyMerge(EqcInfo* e1, TNode t1, EqcInfo* e2, TNode t2)
{
  Assert(e1 != nullptr);
  Assert(e2 != nullptr);
  // check for conflict
  Node conf = checkForMergeConflict(t1, t2, e1, e2);
  if (!conf.isNull())
  {
    InferenceId id = t1.getType().isStringLike()
                         ? InferenceId::STRINGS_PREFIX_CONFLICT
                         : InferenceId::STRINGS_ARITH_BOUND_CONFLICT;
    d_state.setPendingMergeConflict(conf, id);
    return;
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
      Node conf = ei->addEndpointConst(t, c, r == 1);
      if (!conf.isNull())
      {
        d_state.setPendingMergeConflict(conf,
                                        InferenceId::STRINGS_PREFIX_CONFLICT);
        return;
      }
    }
  }
}

Node EagerSolver::checkForMergeConflict(Node a,
                                        Node b,
                                        EqcInfo* ea,
                                        EqcInfo* eb)
{
  Assert(eb != nullptr && ea != nullptr);
  Assert(a.getType() == b.getType());
  Assert(a.getType().isStringLike() || a.getType().isInteger());
  // check prefix, suffix
  for (size_t i = 0; i < 2; i++)
  {
    Node n = i == 0 ? eb->d_firstBound.get() : eb->d_secondBound.get();
    if (!n.isNull())
    {
      Node conf;
      if (a.getType().isStringLike())
      {
        conf = ea->addEndpointConst(n, Node::null(), i == 1);
      }
      else
      {
        Trace("strings-eager-aconf-debug")
            << "addArithmeticBound " << n << " into " << a << " from " << b
            << std::endl;
        conf = addArithmeticBound(ea, n, i == 0);
      }
      if (!conf.isNull())
      {
        return conf;
      }
    }
  }
  return Node::null();
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

Node EagerSolver::addArithmeticBound(EqcInfo* e, Node t, bool isLower)
{
  Assert(e != nullptr);
  Assert(!t.isNull());
  Node tb = t.isConst() ? t : getBoundForLength(t, isLower);
  Assert(!tb.isNull() && tb.getKind() == CONST_RATIONAL)
      << "Unexpected bound " << tb << " from " << t;
  Rational br = tb.getConst<Rational>();
  Node prev = isLower ? e->d_firstBound : e->d_secondBound;
  // check if subsumed
  if (!prev.isNull())
  {
    // convert to bound
    Node prevb = prev.isConst() ? prev : getBoundForLength(prev, isLower);
    Assert(!prevb.isNull() && prevb.getKind() == CONST_RATIONAL);
    Rational prevbr = prevb.getConst<Rational>();
    if (prevbr == br || (br < prevbr) == isLower)
    {
      // subsumed
      return Node::null();
    }
  }
  Node prevo = isLower ? e->d_secondBound : e->d_firstBound;
  Trace("strings-eager-aconf-debug")
      << "Check conflict for bounds " << t << " " << prevo << std::endl;
  if (!prevo.isNull())
  {
    // are we in conflict?
    Node prevob = prevo.isConst() ? prevo : getBoundForLength(prevo, !isLower);
    Assert(!prevob.isNull() && prevob.getKind() == CONST_RATIONAL);
    Rational prevobr = prevob.getConst<Rational>();
    if (prevobr != br && (prevobr < br) == isLower)
    {
      // conflict
      Node ret = EqcInfo::mkMergeConflict(t, prevo);
      Trace("strings-eager-aconf")
          << "String: eager arithmetic bound conflict: " << ret << std::endl;
      return ret;
    }
  }
  if (isLower)
  {
    e->d_firstBound = t;
  }
  else
  {
    e->d_secondBound = t;
  }
  return Node::null();
}

Node EagerSolver::getBoundForLength(Node len, bool isLower)
{
  Assert(len.getKind() == STRING_LENGTH);
  // it is prohibitively expensive to convert to original form and rewrite,
  // since this may invoke the rewriter on lengths of complex terms. Instead,
  // we convert to original term the argument, then call the utility method
  // for computing the length of the argument, implicitly under an application
  // of length (ArithEntail::getConstantBoundLength).
  // convert to original form
  Node olent = SkolemManager::getOriginalForm(len[0]);
  // get the bound
  Node c = d_aent.getConstantBoundLength(olent, isLower);
  Trace("strings-eager-aconf-debug")
      << "Constant " << (isLower ? "lower" : "upper") << " bound for " << len
      << " is " << c << ", from original form " << olent << std::endl;
  return c;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

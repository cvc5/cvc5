/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The eager solver.
 */

#include "theory/strings/eager_solver.h"

#include "options/strings_options.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

EagerSolver::EagerSolver(Env& env, SolverState& state, TermRegistry& treg)
    : EnvObj(env),
      d_state(state),
      d_treg(treg),
      d_aent(env.getRewriter()),
      d_rent(env.getRewriter())
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
  if (checkForMergeConflict(t1, t2, e1, e2))
  {
    return;
  }
}

bool EagerSolver::addEndpointsToEqcInfo(Node t, Node concat, Node eqc)
{
  Assert(concat.getKind() == STRING_CONCAT
         || concat.getKind() == REGEXP_CONCAT);
  EqcInfo* ei = nullptr;
  // check each side
  for (size_t r = 0; r < 2; r++)
  {
    size_t index = r == 0 ? 0 : concat.getNumChildren() - 1;
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
      if (addEndpointConst(ei, t, c, r == 1))
      {
        return true;
      }
    }
  }
  return false;
}

bool EagerSolver::checkForMergeConflict(Node a,
                                        Node b,
                                        EqcInfo* ea,
                                        EqcInfo* eb)
{
  Assert(eb != nullptr && ea != nullptr);
  Assert(a.getType() == b.getType())
      << "bad types for merge " << a << ", " << b;
  // usages of isRealOrInt are only due to subtyping, where seq.nth for
  // sequences of Real are merged to integer equivalence classes
  Assert(a.getType().isStringLike() || a.getType().isRealOrInt());
  // check prefix, suffix
  for (size_t i = 0; i < 2; i++)
  {
    Node n = i == 0 ? eb->d_firstBound.get() : eb->d_secondBound.get();
    if (!n.isNull())
    {
      bool isConflict;
      if (a.getType().isStringLike())
      {
        isConflict = addEndpointConst(ea, n, Node::null(), i == 1);
      }
      else
      {
        Trace("strings-eager-aconf-debug")
            << "addArithmeticBound " << n << " into " << a << " from " << b
            << std::endl;
        isConflict = addArithmeticBound(ea, n, i == 0);
      }
      if (isConflict)
      {
        return true;
      }
    }
  }
  return false;
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
      // add prefix constraints
      if (addEndpointsToEqcInfo(atom, atom[1], eqc))
      {
        // conflict, we are done
        return;
      }
      else if (!options().strings.stringsEagerLenEntRegexp)
      {
        // do not infer length constraints if option is disabled
        return;
      }
      // also infer length constraints if the first is a variable
      if (atom[0].isVar())
      {
        EqcInfo* blenEqc = nullptr;
        for (size_t i = 0; i < 2; i++)
        {
          bool isLower = (i == 0);
          Node b = d_rent.getConstantBoundLengthForRegexp(atom[1], isLower);
          if (!b.isNull())
          {
            if (blenEqc == nullptr)
            {
              Node lenTerm =
                  NodeManager::currentNM()->mkNode(STRING_LENGTH, atom[0]);
              if (!ee->hasTerm(lenTerm))
              {
                break;
              }
              lenTerm = ee->getRepresentative(lenTerm);
              blenEqc = d_state.getOrMakeEqcInfo(lenTerm);
            }
            if (addArithmeticBound(blenEqc, atom, isLower))
            {
              return;
            }
          }
        }
      }
    }
  }
}

bool EagerSolver::addEndpointConst(EqcInfo* e, Node t, Node c, bool isSuf)
{
  Assert(e != nullptr);
  Assert(!t.isNull());
  Node conf = e->addEndpointConst(t, c, isSuf);
  if (!conf.isNull())
  {
    d_state.setPendingMergeConflict(
        conf, InferenceId::STRINGS_PREFIX_CONFLICT, isSuf);
    return true;
  }
  return false;
}

bool EagerSolver::addArithmeticBound(EqcInfo* e, Node t, bool isLower)
{
  Trace("strings-eager-aconf-debug")
      << "addArithmeticBound " << t << ", isLower = " << isLower << "..."
      << std::endl;
  Assert(e != nullptr);
  Assert(!t.isNull());
  Node tb = t.isConst() ? t : getBoundForLength(t, isLower);
  Assert(!tb.isNull() && tb.isConst() && tb.getType().isRealOrInt())
      << "Unexpected bound " << tb << " from " << t;
  Rational br = tb.getConst<Rational>();
  Node prev = isLower ? e->d_firstBound : e->d_secondBound;
  // check if subsumed
  if (!prev.isNull())
  {
    // convert to bound
    Node prevb = prev.isConst() ? prev : getBoundForLength(prev, isLower);
    Assert(!prevb.isNull() && prevb.isConst() && prevb.getType().isRealOrInt());
    Rational prevbr = prevb.getConst<Rational>();
    if (prevbr == br || (br < prevbr) == isLower)
    {
      // subsumed
      return false;
    }
  }
  Node prevo = isLower ? e->d_secondBound : e->d_firstBound;
  Trace("strings-eager-aconf-debug")
      << "Check conflict for bounds " << t << " " << prevo << std::endl;
  if (!prevo.isNull())
  {
    // are we in conflict?
    Node prevob = prevo.isConst() ? prevo : getBoundForLength(prevo, !isLower);
    Assert(!prevob.isNull() && prevob.isConst()
           && prevob.getType().isRealOrInt());
    Rational prevobr = prevob.getConst<Rational>();
    Trace("strings-eager-aconf-debug")
        << "Previous opposite bound was " << prevobr << ", current bound is "
        << br << ", isLower = " << isLower << std::endl;
    if (prevobr != br && (prevobr < br) == isLower)
    {
      // conflict
      Node ret = EqcInfo::mkMergeConflict(t, prevo, true);
      Trace("strings-eager-aconf")
          << "String: eager arithmetic bound conflict: " << ret << std::endl;
      d_state.setPendingMergeConflict(
          ret, InferenceId::STRINGS_ARITH_BOUND_CONFLICT);
      return true;
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
  return false;
}

Node EagerSolver::getBoundForLength(Node t, bool isLower) const
{
  if (t.getKind() == STRING_IN_REGEXP)
  {
    return d_rent.getConstantBoundLengthForRegexp(t[1], isLower);
  }
  Assert(t.getKind() == STRING_LENGTH);
  // it is prohibitively expensive to convert to original form and rewrite,
  // since this may invoke the rewriter on lengths of complex terms. Instead,
  // we convert to original term the argument, then call the utility method
  // for computing the length of the argument, implicitly under an application
  // of length (ArithEntail::getConstantBoundLength).
  // convert to original form
  Node olent = SkolemManager::getOriginalForm(t[0]);
  // get the bound
  Node c = d_aent.getConstantBoundLength(olent, isLower);
  Trace("strings-eager-aconf-debug")
      << "Constant " << (isLower ? "lower" : "upper") << " bound for " << t
      << " is " << c << ", from original form " << olent << std::endl;
  return c;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

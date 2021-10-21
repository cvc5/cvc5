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
  if (k == STRING_LENGTH || k == STRING_TO_CODE)
  {
    eq::EqualityEngine* ee = d_state.getEqualityEngine();
    Node r = ee->getRepresentative(t[0]);
    EqcInfo* ei = d_state.getOrMakeEqcInfo(r);
    if (k == STRING_LENGTH)
    {
      ei->d_lengthTerm = t;
      // also assume it as upper/lower bound as applicable for the equivalence
      // class info of t.
      EqcInfo* eil = nullptr;
      for (size_t i=0; i<2; i++)
      {
        Node b = getBoundForLength(t, i==0);
        if (b.isNull())
        {
          continue;
        }
        if (eil == nullptr)
        {
          eil = d_state.getOrMakeEqcInfo(t);
        }
        if (i==0)
        {
          eil->d_prefixC = t;
        }
        else if (i==1)
        {
          eil->d_suffixC = t;
        }
      }
    }
    else
    {
      ei->d_codeTerm = t[0];
    }
  }
  else if (t.isConst())
  {
    TypeNode tn = t.getType();
    if (tn.isStringLike() || tn.isInteger())
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
  // always create it if e2 was non-null
  EqcInfo* e1 = d_state.getOrMakeEqcInfo(t1);
  // check for conflict
  Node conf = checkForMergeConflict(t1, t2, e1, e2);
  if (!conf.isNull())
  {
    d_state.setPendingMergeConflict(conf);
    return;
  }
  // add information from e2 to e1
  if (!e2->d_lengthTerm.get().isNull())
  {
    e1->d_lengthTerm.set(e2->d_lengthTerm);
  }
  if (!e2->d_codeTerm.get().isNull())
  {
    e1->d_codeTerm.set(e2->d_codeTerm);
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
      Node conf = ei->addEndpointConst(t, c, r == 1);
      if (!conf.isNull())
      {
        d_state.setPendingMergeConflict(conf);
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
  Assert(a.getType() == b.getType());
  TypeNode tn = a.getType();
  if (tn.isStringLike())
  {
    if (eb != nullptr)
    {
      // we always create ea if eb exists
      Assert(ea != nullptr);
      // check prefix, suffix
      for (size_t i = 0; i < 2; i++)
      {
        Node n = i == 0 ? eb->d_prefixC.get() : eb->d_suffixC.get();
        if (!n.isNull())
        {
          Node conf = ea->addEndpointConst(n, Node::null(), i == 1);
          if (!conf.isNull())
          {
            return conf;
          }
        }
      }
    }
  }
  else if (tn.isInteger())
  {
    // TODO
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

Node EagerSolver::getBoundForLength(Node len, bool isLower)
{
  Assert (len.getKind()==STRING_LENGTH);
  std::map<Node, Node>& cache = d_boundCache[isLower ? 0 : 1];
  std::map<Node, Node>::iterator it = cache.find(len);
  if (it!=cache.end())
  {
    return it->second;
  }
  // convert to original form
  Node olen = SkolemManager::getOriginalForm(len);
  olen = rewrite(olen);
  Node c = d_aent.getConstantBound(olen, isLower);
  cache[len] = c;
  Trace("strings-eager-aconf-debug") << "Constant " << (isLower ? "lower" : "upper") << " bound for " << len << " is " << c << std::endl;
  return c;
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5

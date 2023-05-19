/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term evaluator class.
 */

#include "theory/quantifiers/ieval/term_evaluator.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/ieval/state.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

TermEvaluator::TermEvaluator(Env& env, TermEvaluatorMode tev)
    : EnvObj(env), d_tevMode(tev)
{
}

TermEvaluatorEntailed::TermEvaluatorEntailed(Env& env,
                                             TermEvaluatorMode tev,
                                             QuantifiersState& qs,
                                             TermDb& tdb)
    : TermEvaluator(env, tev), d_qs(qs), d_tdb(tdb), d_checkRelDom(false)
{
  // check relevant domain during partial evaluation
  d_checkRelDom =
      (tev == TermEvaluatorMode::CONFLICT || tev == TermEvaluatorMode::PROP);
}

TNode TermEvaluatorEntailed::evaluateBase(const State& s, TNode n)
{
  if (n.getKind() == FORALL)
  {
    return s.getSome();
  }
  // if unknown, it is none
  return d_qs.hasTerm(n) ? d_qs.getRepresentative(n) : s.getNone();
}

TNode TermEvaluatorEntailed::partialEvaluateChild(
    const State& s, TNode n, TNode child, TNode val, Node& exp)
{
  // if a Boolean connective, handle short circuiting
  Kind k = n.getKind();
  // Implies and xor are eliminated from the propositional skeleton of
  // quantifier bodies, so we don't check for them here. They still may
  // occur e.g. as arguments to parameteric operators involving Bool.
  if (k == AND || k == OR)
  {
    if (val.isConst() && val.getConst<bool>() == (k == OR))
    {
      // the value determines the value of this
      Trace("ieval-state-debug") << "...short circuit " << val << std::endl;
      exp = child;
      return val;
    }
  }
  else if (k == NOT)
  {
    if (val.isConst())
    {
      NodeManager* nm = NodeManager::currentNM();
      val = nm->mkConst(!val.getConst<bool>());
    }
    Trace("ieval-state-debug") << "...eval negation " << val << std::endl;
    return val;
  }
  else if (k == ITE)
  {
    // if the condition is being set, and the branch already has a value,
    // then this has the value of the branch.
    if (n[0] == child)
    {
      if (val.isConst())
      {
        bool pol = val.getConst<bool>();
        Node vbranch = s.getValue(n[pol ? 1 : 2]);
        if (!vbranch.isNull())
        {
          Trace("ieval-state-debug")
              << "...branched to " << vbranch << std::endl;
          return vbranch;
        }
      }
    }
    else
    {
      // if the branch is being set, the condition is determined, and it is
      // the relevant branch, then this value is val.
      Node vcond = s.getValue(n[0]);
      if (!vcond.isNull() && vcond.isConst())
      {
        if (child == n[vcond.getConst<bool>() ? 1 : 2])
        {
          Trace("ieval-state-debug")
              << "...relevant branch " << val << std::endl;
          return val;
        }
      }
    }
    return Node::null();
  }
  else if (s.isNone(val))
  {
    // none on either side of equality, or for any child of any other
    // operator is automatic none
    Trace("ieval-state-debug") << "...none default" << std::endl;
    exp = child;
    return val;
  }
  // if we are not in the relevant domain, we are immediately "none". We only
  // do this if we are in conflict/prop mode
  if (d_checkRelDom)
  {
    TNode mop = d_tdb.getMatchOperator(n);
    if (!mop.isNull())
    {
      // scan the argument list of n to find occurrences of the child
      for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
      {
        if (n[i] == child && !d_tdb.inRelevantDomain(mop, i, val))
        {
          exp = child;
          return s.getNone();
        }
      }
    }
  }
  // NOTE: could do other short circuiting like zero for mult, this is omitted
  // for the sake of simplicity.
  return Node::null();
}

TNode TermEvaluatorEntailed::evaluate(const State& s,
                                      TNode n,
                                      const std::vector<TNode>& childValues)
{
  // set to unknown, handle cases
  TNode ret = s.getNone();
  // if an existing ground term, just return representative
  if (!expr::hasBoundVar(n) && d_qs.hasTerm(n))
  {
    return d_qs.getRepresentative(n);
  }
  TNode mop = d_tdb.getMatchOperator(n);
  if (!mop.isNull())
  {
    // see if we are congruent to a term known by the term database
    Node eval = d_tdb.getCongruentTerm(mop, childValues);
    if (!eval.isNull())
    {
      ret = d_qs.getRepresentative(eval);
      // Note that ret may be an (unassigned, non-constant) Boolean. We do
      // not turn this into "none" here yet.
    }
    return ret;
  }

  Kind k = n.getKind();
  NodeManager* nm = NodeManager::currentNM();
  Assert(k != NOT);
  if (k == AND || k == OR)
  {
    bool hasSome = false;
    for (TNode cvalue : childValues)
    {
      if (s.isSome(cvalue))
      {
        hasSome = true;
      }
      else if (!cvalue.isConst())
      {
        // unknown (possibly none), we are done
        Trace("ieval-state-debug") << "...unknown child of AND/OR" << std::endl;
        return ret;
      }
      else
      {
        Assert(cvalue.isConst());
      }
    }
    // if any child is some, we are some as well
    ret = hasSome ? Node(s.getSome()) : nm->mkConst(k == AND);
    Trace("ieval-state-debug") << "...exhausted AND/OR" << std::endl;
  }
  else if (k == EQUAL)
  {
    // this handles any type EQUAL. If either side is none, we should have
    // short circuited above.
    // Otherwise, we handle cases below.
    for (TNode cvalue : childValues)
    {
      Assert(!s.isNone(cvalue));
      if (s.isSome(cvalue))
      {
        // (= some t) --> some, where we assume that t is not none.
        Trace("ieval-state-debug") << "...some equal via some" << std::endl;
        return cvalue;
      }
    }
    // if both side evaluate, we evaluate to true if both sides are
    // equal, false the values are disequal (which includes checking
    // if cval1 and cval2 are distinct constants), and do not evaluate
    // otherwise.
    if (d_qs.areEqual(childValues[0], childValues[1]))
    {
      ret = nm->mkConst(true);
      Trace("ieval-state-debug")
          << "...equal via " << childValues[0] << std::endl;
    }
    else if (d_qs.areDisequal(childValues[0], childValues[1]))
    {
      Trace("ieval-state-debug") << "...disequal " << childValues[0]
                                 << " != " << childValues[1] << std::endl;
      ret = nm->mkConst(false);
    }
    else
    {
      Trace("ieval-state-debug") << "...unknown equal" << std::endl;
      // otherwise we don't evaluate. This is different from marking
      // it as "none", since we want to propagate equalities between
      // known terms.
      return s.getSome();
    }
  }
  else if (k == ITE)
  {
    TNode cval1 = childValues[0];
    Assert(!cval1.isNull());
    if (cval1.isConst())
    {
      // if condition evaluates, get value of branch
      ret = childValues[cval1.getConst<bool>() ? 1 : 2];
      Trace("ieval-state-debug") << "...take branch " << ret << std::endl;
    }
    else
    {
      // otherwise, we only are known if the branches are equal
      TNode cval2 = childValues[1];
      TNode cval3 = childValues[2];
      Assert(!cval2.isNull());
      Assert(!cval3.isNull());
      // this handles any type ITE
      if (cval2 == cval3)
      {
        // if the conditions are equal, take their value except that
        // (ite none some some) ---> none.
        if (!s.isNone(cval1) || !s.isSome(cval2))
        {
          // (ite none t t) ---> t
          // (ite some t t) ---> t
          // (ite some some some) ---> some
          ret = cval2;
          Trace("ieval-state-debug")
              << "...equal branches " << cval2 << std::endl;
        }
      }
      else if (!s.isNone(cval1) && !s.isNone(cval2) && !s.isNone(cval3))
      {
        if (s.isSome(cval2) || s.isSome(cval3))
        {
          // (ite some t some) ---> some
          // (ite some some t) ---> some
          ret = s.getSome();
          Trace("ieval-state-debug") << "...branch with some" << std::endl;
        }
        else
        {
          // (ite some t1 t2) ---> some
          ret = s.getSome();
          Trace("ieval-state-debug")
              << "...different known branches" << std::endl;
        }
      }
    }
  }
  else
  {
    for (TNode cvalue : childValues)
    {
      Assert(!cvalue.isNull());
      if (s.isSome(cvalue))
      {
        Trace("ieval-state-debug")
            << "...some child of evaluated term" << std::endl;
        return ret;
      }
    }
    Node preTerm;
    // see if we can rewrite?
    if (n.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      std::vector<TNode> pcv;
      pcv.push_back(n.getOperator());
      pcv.insert(pcv.end(), childValues.begin(), childValues.end());
      preTerm = nm->mkNode(n.getKind(), pcv);
    }
    else
    {
      preTerm = nm->mkNode(n.getKind(), childValues);
    }
    Node npr = s.doRewrite(preTerm);
    ret = evaluateBase(s, npr);
    Trace("ieval-state-debug") << "...evaluate + find " << ret << std::endl;
  }
  // NOTE: could do theory entailment checks here, although this is omitted
  // for the sake of performance.
  return ret;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

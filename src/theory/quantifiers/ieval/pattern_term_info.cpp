/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per pattern term in CCFV.
 */

#include "theory/quantifiers/ieval/pattern_term_info.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/ieval/state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

PatTermInfo::PatTermInfo(context::Context* c)
    : d_eq(c),
      d_numUnassigned(c, 0),
      d_numChildren(0),
      d_parentNotify(c),
      d_isWatchedEval(c, false)
{
}

void PatTermInfo::initialize(TNode pattern, TermDb* tdb)
{
  Assert(!pattern.isNull());
  d_pattern = pattern;
  d_matchOp = tdb->getMatchOperator(pattern);
}

bool PatTermInfo::isActive() const { return d_eq.get().isNull(); }

bool PatTermInfo::notifyChild(State& s, TNode child, TNode val)
{
  Assert(!val.isNull());
  Assert(s.isGroundEqc(val) || s.isNone(val));
  if (!d_eq.get().isNull())
  {
    // already set
    return false;
  }
  if (!d_matchOp.isNull())
  {
    // for congruence terms
    // if the value of a child is unknown, we are now unknown
    if (s.isNone(val))
    {
      d_eq = val;
      return true;
    }
    // TODO: could propagate `some`? This would be in rare cases where
    // a Boolean term was a child of a term. Even so, Boolean terms would
    // not work with evaluation due to use of Boolean term variables.
  }
  else
  {
    Trace("ieval-state-debug")
        << "Notify interpreted fun: " << d_pattern << " child " << child
        << " == " << val << std::endl;
    // if a Boolean connective, handle short circuiting
    Kind k = d_pattern.getKind();
    // implies and xor are eliminated from quantifier bodies
    Assert(k != IMPLIES && k != XOR);
    if (k == AND || k == OR)
    {
      if (val.isConst() && val.getConst<bool>() == (k == OR))
      {
        // the value determines the value of this
        d_eq = val;
        Trace("ieval-state-debug") << "...short circuit " << val << std::endl;
        return true;
      }
    }
    else if (k == NOT)
    {
      if (val.isConst())
      {
        NodeManager* nm = NodeManager::currentNM();
        d_eq = nm->mkConst(!val.getConst<bool>());
      }
      else
      {
        d_eq = val;
      }
      Trace("ieval-state-debug")
          << "...eval negation " << d_eq.get() << std::endl;
      return true;
    }
    else if (k == ITE)
    {
      // if the condition is being set, and the branch already has a value,
      // then this has the value of the branch.
      if (d_pattern[0] == child)
      {
        if (val.isConst())
        {
          bool pol = val.getConst<bool>();
          Node vbranch = s.getValue(d_pattern[pol ? 1 : 2]);
          if (!vbranch.isNull())
          {
            d_eq = vbranch;
            Trace("ieval-state-debug")
                << "...branched to " << vbranch << std::endl;
            return true;
          }
        }
      }
      else
      {
        // if the branch is being set, the condition is determined, and it is
        // the relevant branch, then this value is val.
        Node vcond = s.getValue(d_pattern[0]);
        if (!vcond.isNull() && vcond.isConst())
        {
          if (child == d_pattern[vcond.getConst<bool>() ? 1 : 2])
          {
            d_eq = val;
            Trace("ieval-state-debug")
                << "...relevant branch " << val << std::endl;
            return true;
          }
        }
      }
    }
    else
    {
      if (s.isNone(val))
      {
        // none on either side of equality, or for any child of any other
        // operator is automatic none
        d_eq = val;
        Trace("ieval-state-debug") << "...none default" << std::endl;
        return true;
      }
    }
    // if a Boolean connective, we can possibly evaluate
    Assert(d_numUnassigned.get() > 0);
    d_numUnassigned = d_numUnassigned.get() - 1;
    Trace("ieval-state-debug")
        << "...unassigned children now " << d_numUnassigned << std::endl;
    if (d_numUnassigned == 0)
    {
      // set to unknown, handle cases
      d_eq = s.getNone();
      NodeManager* nm = NodeManager::currentNM();
      Assert(k != NOT);
      if (k == AND || k == OR)
      {
        bool hasSome = false;
        for (TNode pc : d_pattern)
        {
          TNode cvalue = s.getValue(pc);
          Assert(!cvalue.isNull());
          if (s.isNone(cvalue))
          {
            // unknown, we are done
            Trace("ieval-state-debug")
                << "...unknown child of AND/OR" << std::endl;
            return true;
          }
          else if (s.isSome(cvalue))
          {
            hasSome = true;
          }
          else
          {
            Assert(cvalue.isConst());
          }
        }
        // if any child is some, we are some as well
        d_eq = hasSome ? s.getSome() : nm->mkConst(k == AND);
        Trace("ieval-state-debug") << "...exhausted AND/OR" << std::endl;
      }
      else if (k == EQUAL)
      {
        // this handles any type EQUAL. If either side is none, we should have
        // short circuited above.
        // Otherwise, we handle cases below.
        TNode cval[2];
        for (size_t i = 0; i < 2; i++)
        {
          cval[i] = s.getValue(d_pattern[i]);
          Assert(!cval[i].isNull() && !s.isNone(cval[i]));
          if (s.isSome(cval[i]))
          {
            // (= some t) --> some, where we assume that t is not none.
            d_eq = cval[i];
            Trace("ieval-state-debug") << "...some equal via some" << std::endl;
            return true;
          }
        }
        // if both side evaluate, we evaluate to true if both sides are
        // equal, false the values are disequal (which includes checking
        // if cval1 and cval2 are distinct constants), and do not evaluate
        // otherwise.
        if (cval[0] == cval[1])
        {
          d_eq = nm->mkConst(true);
          Trace("ieval-state-debug") << "...equal via " << cval[0] << std::endl;
        }
        else if (s.areDisequal(cval[0], cval[1]))
        {
          Trace("ieval-state-debug")
              << "...disequal " << cval[0] << " != " << cval[1] << std::endl;
          d_eq = nm->mkConst(false);
        }
        else
        {
          Trace("ieval-state-debug") << "...unknown equal" << std::endl;
          // otherwise we don't evaluate. This is different from marking
          // it as "none", since we want to propagate equalities between
          // known terms. Notice that Booleans require being assigned to
          // constants, so this only applies to non-Boolean equalities.
          Assert(!val.getType().isBoolean());
          d_eq = s.getSome();
          return true;
        }
      }
      else if (k == ITE)
      {
        TNode cval1 = s.getValue(d_pattern[0]);
        Assert(!cval1.isNull());
        Assert(cval1.isConst() || s.isNone(cval1) || s.isSome(cval1));
        if (cval1.isConst())
        {
          // if condition evaluates, get value of branch
          d_eq = s.getValue(d_pattern[cval1.getConst<bool>() ? 1 : 2]);
          Trace("ieval-state-debug")
              << "...take branch " << d_eq.get() << std::endl;
        }
        else
        {
          // otherwise, we only are known if the branches are equal
          TNode cval2 = s.getValue(d_pattern[1]);
          TNode cval3 = s.getValue(d_pattern[2]);
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
              d_eq = cval2;
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
              d_eq = s.getSome();
              Trace("ieval-state-debug") << "...branch with some" << std::endl;
            }
            else
            {
              // (ite some t1 t2) ---> some
              d_eq = s.getSome();
              Trace("ieval-state-debug")
                  << "...different known branches" << std::endl;
            }
          }
        }
      }
      else
      {
        // see if we can rewrite?
        std::vector<Node> args;
        if (d_pattern.getMetaKind() == kind::metakind::PARAMETERIZED)
        {
          args.push_back(d_pattern.getOperator());
        }
        bool success = true;
        for (TNode pc : d_pattern)
        {
          TNode cvalue = s.getValue(pc);
          Assert(!cvalue.isNull());
          if (s.isSome(cvalue))
          {
            Trace("ieval-state-debug")
                << "...some child of evaluated term" << std::endl;
            success = false;
            break;
          }
          args.push_back(cvalue);
        }
        if (success)
        {
          Node npattern = nm->mkNode(d_pattern.getKind(), args);
          Node npr = s.doRewrite(npattern);
          npr = s.getGroundRepresentative(npr);
          if (!npr.isNull())
          {
            d_eq = npr;
            Trace("ieval-state-debug")
                << "...evaluate + find " << npr << std::endl;
          }
          else
          {
            Trace("ieval-state-debug")
                << "...failed to evaluate + find " << npattern << std::endl;
          }
        }
      }
      // TODO: entailment check?
      return true;
    }
  }
  return false;
}

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

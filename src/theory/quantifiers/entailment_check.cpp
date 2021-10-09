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
 * Implementation of entailment check class.
 */

#include "theory/quantifiers/entailment_check.h"

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
namespace theory {
namespace quantifiers {

EntailmentCheck::EntailmentCheck(Env& env, QuantifiersState& qs, TermDb& tdb)
    : EnvObj(env), d_qstate(qs), d_tdb(tdb)
{
}

EntailmentCheck::~EntailmentCheck() {}
Node EntailmentCheck::evaluateTerm2(TNode n,
                                    std::map<TNode, Node>& visited,
                                    std::vector<Node>& exp,
                                    bool useEntailmentTests,
                                    bool computeExp,
                                    bool reqHasTerm)
{
  std::map<TNode, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    return itv->second;
  }
  size_t prevSize = exp.size();
  Trace("term-db-eval") << "evaluate term : " << n << std::endl;
  Node ret = n;
  if (n.getKind() == FORALL || n.getKind() == BOUND_VARIABLE)
  {
    // do nothing
  }
  else if (d_qstate.hasTerm(n))
  {
    Trace("term-db-eval") << "...exists in ee, return rep" << std::endl;
    ret = d_qstate.getRepresentative(n);
    if (computeExp)
    {
      if (n != ret)
      {
        exp.push_back(n.eqNode(ret));
      }
    }
    reqHasTerm = false;
  }
  else if (n.hasOperator())
  {
    std::vector<TNode> args;
    bool ret_set = false;
    Kind k = n.getKind();
    std::vector<Node> tempExp;
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      TNode c = evaluateTerm2(
          n[i], visited, tempExp, useEntailmentTests, computeExp, reqHasTerm);
      if (c.isNull())
      {
        ret = Node::null();
        ret_set = true;
        break;
      }
      else if (c == d_true || c == d_false)
      {
        // short-circuiting
        if ((k == AND && c == d_false) || (k == OR && c == d_true))
        {
          ret = c;
          ret_set = true;
          reqHasTerm = false;
          break;
        }
        else if (k == ITE && i == 0)
        {
          ret = evaluateTerm2(n[c == d_true ? 1 : 2],
                              visited,
                              tempExp,
                              useEntailmentTests,
                              computeExp,
                              reqHasTerm);
          ret_set = true;
          reqHasTerm = false;
          break;
        }
      }
      if (computeExp)
      {
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
      Trace("term-db-eval") << "  child " << i << " : " << c << std::endl;
      args.push_back(c);
    }
    if (ret_set)
    {
      // if we short circuited
      if (computeExp)
      {
        exp.clear();
        exp.insert(exp.end(), tempExp.begin(), tempExp.end());
      }
    }
    else
    {
      // get the (indexed) operator of n, if it exists
      TNode f = getMatchOperator(n);
      // if it is an indexed term, return the congruent term
      if (!f.isNull())
      {
        // if f is congruent to a term indexed by this class
        TNode nn = getCongruentTerm(f, args);
        Trace("term-db-eval") << "  got congruent term " << nn
                              << " from DB for " << n << std::endl;
        if (!nn.isNull())
        {
          if (computeExp)
          {
            Assert(nn.getNumChildren() == n.getNumChildren());
            for (unsigned i = 0, nchild = nn.getNumChildren(); i < nchild; i++)
            {
              if (nn[i] != n[i])
              {
                exp.push_back(nn[i].eqNode(n[i]));
              }
            }
          }
          ret = d_qstate.getRepresentative(nn);
          Trace("term-db-eval") << "return rep" << std::endl;
          ret_set = true;
          reqHasTerm = false;
          Assert(!ret.isNull());
          if (computeExp)
          {
            if (n != ret)
            {
              exp.push_back(nn.eqNode(ret));
            }
          }
        }
      }
      if (!ret_set)
      {
        Trace("term-db-eval") << "return rewrite" << std::endl;
        // a theory symbol or a new UF term
        if (n.getMetaKind() == metakind::PARAMETERIZED)
        {
          args.insert(args.begin(), n.getOperator());
        }
        ret = NodeManager::currentNM()->mkNode(n.getKind(), args);
        ret = rewrite(ret);
        if (ret.getKind() == EQUAL)
        {
          if (d_qstate.areDisequal(ret[0], ret[1]))
          {
            ret = d_false;
          }
        }
        if (useEntailmentTests)
        {
          if (ret.getKind() == EQUAL || ret.getKind() == GEQ)
          {
            Valuation& val = d_qstate.getValuation();
            for (unsigned j = 0; j < 2; j++)
            {
              std::pair<bool, Node> et = val.entailmentCheck(
                  options::TheoryOfMode::THEORY_OF_TYPE_BASED,
                  j == 0 ? ret : ret.negate());
              if (et.first)
              {
                ret = j == 0 ? d_true : d_false;
                if (computeExp)
                {
                  exp.push_back(et.second);
                }
                break;
              }
            }
          }
        }
      }
    }
  }
  // must have the term
  if (reqHasTerm && !ret.isNull())
  {
    Kind k = ret.getKind();
    if (k != OR && k != AND && k != EQUAL && k != ITE && k != NOT
        && k != FORALL)
    {
      if (!d_qstate.hasTerm(ret))
      {
        ret = Node::null();
      }
    }
  }
  Trace("term-db-eval") << "evaluated term : " << n << ", got : " << ret
                        << ", reqHasTerm = " << reqHasTerm << std::endl;
  // clear the explanation if failed
  if (computeExp && ret.isNull())
  {
    exp.resize(prevSize);
  }
  visited[n] = ret;
  return ret;
}

TNode EntailmentCheck::getEntailedTerm2(TNode n,
                                        std::map<TNode, TNode>& subs,
                                        bool subsRep,
                                        bool hasSubs)
{
  Trace("term-db-entail") << "get entailed term : " << n << std::endl;
  if (d_qstate.hasTerm(n))
  {
    Trace("term-db-entail") << "...exists in ee, return rep " << std::endl;
    return n;
  }
  else if (n.getKind() == BOUND_VARIABLE)
  {
    if (hasSubs)
    {
      std::map<TNode, TNode>::iterator it = subs.find(n);
      if (it != subs.end())
      {
        Trace("term-db-entail")
            << "...substitution is : " << it->second << std::endl;
        if (subsRep)
        {
          Assert(d_qstate.hasTerm(it->second));
          Assert(d_qstate.getRepresentative(it->second) == it->second);
          return it->second;
        }
        return getEntailedTerm2(it->second, subs, subsRep, hasSubs);
      }
    }
  }
  else if (n.getKind() == ITE)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], subs, subsRep, hasSubs, i == 0))
      {
        return getEntailedTerm2(n[i == 0 ? 1 : 2], subs, subsRep, hasSubs);
      }
    }
  }
  else
  {
    if (n.hasOperator())
    {
      TNode f = getMatchOperator(n);
      if (!f.isNull())
      {
        std::vector<TNode> args;
        for (unsigned i = 0; i < n.getNumChildren(); i++)
        {
          TNode c = getEntailedTerm2(n[i], subs, subsRep, hasSubs);
          if (c.isNull())
          {
            return TNode::null();
          }
          c = d_qstate.getRepresentative(c);
          Trace("term-db-entail") << "  child " << i << " : " << c << std::endl;
          args.push_back(c);
        }
        TNode nn = getCongruentTerm(f, args);
        Trace("term-db-entail")
            << "  got congruent term " << nn << " for " << n << std::endl;
        return nn;
      }
    }
  }
  return TNode::null();
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  std::vector<Node> exp;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, false, reqHasTerm);
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   std::vector<Node>& exp,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  return evaluateTerm2(n, visited, exp, useEntailmentTests, true, reqHasTerm);
}

TNode EntailmentCheck::getEntailedTerm(TNode n,
                                       std::map<TNode, TNode>& subs,
                                       bool subsRep)
{
  return getEntailedTerm2(n, subs, subsRep, true);
}

TNode EntailmentCheck::getEntailedTerm(TNode n)
{
  std::map<TNode, TNode> subs;
  return getEntailedTerm2(n, subs, false, false);
}

bool EntailmentCheck::isEntailed2(
    TNode n, std::map<TNode, TNode>& subs, bool subsRep, bool hasSubs, bool pol)
{
  Trace("term-db-entail") << "Check entailed : " << n << ", pol = " << pol
                          << std::endl;
  Assert(n.getType().isBoolean());
  if (n.getKind() == EQUAL && !n[0].getType().isBoolean())
  {
    TNode n1 = getEntailedTerm2(n[0], subs, subsRep, hasSubs);
    if (!n1.isNull())
    {
      TNode n2 = getEntailedTerm2(n[1], subs, subsRep, hasSubs);
      if (!n2.isNull())
      {
        if (n1 == n2)
        {
          return pol;
        }
        else
        {
          Assert(d_qstate.hasTerm(n1));
          Assert(d_qstate.hasTerm(n2));
          if (pol)
          {
            return d_qstate.areEqual(n1, n2);
          }
          else
          {
            return d_qstate.areDisequal(n1, n2);
          }
        }
      }
    }
  }
  else if (n.getKind() == NOT)
  {
    return isEntailed2(n[0], subs, subsRep, hasSubs, !pol);
  }
  else if (n.getKind() == OR || n.getKind() == AND)
  {
    bool simPol = (pol && n.getKind() == OR) || (!pol && n.getKind() == AND);
    for (unsigned i = 0; i < n.getNumChildren(); i++)
    {
      if (isEntailed2(n[i], subs, subsRep, hasSubs, pol))
      {
        if (simPol)
        {
          return true;
        }
      }
      else
      {
        if (!simPol)
        {
          return false;
        }
      }
    }
    return !simPol;
    // Boolean equality here
  }
  else if (n.getKind() == EQUAL || n.getKind() == ITE)
  {
    for (unsigned i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], subs, subsRep, hasSubs, i == 0))
      {
        unsigned ch = (n.getKind() == EQUAL || i == 0) ? 1 : 2;
        bool reqPol = (n.getKind() == ITE || i == 0) ? pol : !pol;
        return isEntailed2(n[ch], subs, subsRep, hasSubs, reqPol);
      }
    }
  }
  else if (n.getKind() == APPLY_UF)
  {
    TNode n1 = getEntailedTerm2(n, subs, subsRep, hasSubs);
    if (!n1.isNull())
    {
      Assert(d_qstate.hasTerm(n1));
      if (n1 == d_true)
      {
        return pol;
      }
      else if (n1 == d_false)
      {
        return !pol;
      }
      else
      {
        return d_qstate.getRepresentative(n1) == (pol ? d_true : d_false);
      }
    }
  }
  else if (n.getKind() == FORALL && !pol)
  {
    return isEntailed2(n[1], subs, subsRep, hasSubs, pol);
  }
  return false;
}

bool EntailmentCheck::isEntailed(TNode n, bool pol)
{
  Assert(d_consistent_ee);
  std::map<TNode, TNode> subs;
  return isEntailed2(n, subs, false, false, pol);
}

bool EntailmentCheck::isEntailed(TNode n,
                                 std::map<TNode, TNode>& subs,
                                 bool subsRep,
                                 bool pol)
{
  Assert(d_consistent_ee);
  return isEntailed2(n, subs, subsRep, true, pol);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

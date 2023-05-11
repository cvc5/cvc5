/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of entailment check class.
 */

#include "theory/quantifiers/entailment_check.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EntailmentCheck::EntailmentCheck(Env& env, QuantifiersState& qs, TermDb& tdb)
    : EnvObj(env), d_qstate(qs), d_tdb(tdb)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

EntailmentCheck::~EntailmentCheck() {}

Node EntailmentCheck::evaluateTerm2(TNode n,
                                    std::map<TNode, Node>& visited,
                                    std::map<TNode, TNode>& subs,
                                    bool subsRep,
                                    bool useEntailmentTests,
                                    bool reqHasTerm)
{
  std::map<TNode, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    return itv->second;
  }
  Trace("term-db-eval") << "evaluate term : " << n << std::endl;
  Node ret = n;
  Kind k = n.getKind();
  if (k == FORALL)
  {
    // do nothing
  }
  else if (k == BOUND_VARIABLE)
  {
    std::map<TNode, TNode>::iterator it = subs.find(n);
    if (it != subs.end())
    {
      if (!subsRep)
      {
        ret = d_qstate.getRepresentative(it->second);
      }
      else
      {
        ret = it->second;
      }
    }
  }
  else if (d_qstate.hasTerm(n))
  {
    Trace("term-db-eval") << "...exists in ee, return rep" << std::endl;
    ret = d_qstate.getRepresentative(n);
    reqHasTerm = false;
  }
  else if (n.hasOperator())
  {
    std::vector<TNode> args;
    bool ret_set = false;
    for (unsigned i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      TNode c = evaluateTerm2(
          n[i], visited, subs, subsRep, useEntailmentTests, reqHasTerm);
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
                              subs,
                              subsRep,
                              useEntailmentTests,
                              reqHasTerm);
          ret_set = true;
          reqHasTerm = false;
          break;
        }
      }
      Trace("term-db-eval") << "  child " << i << " : " << c << std::endl;
      args.push_back(c);
    }
    if (!ret_set)
    {
      // get the (indexed) operator of n, if it exists
      TNode f = d_tdb.getMatchOperator(n);
      // if it is an indexed term, return the congruent term
      if (!f.isNull())
      {
        // if f is congruent to a term indexed by this class
        TNode nn = d_tdb.getCongruentTerm(f, args);
        Trace("term-db-eval") << "  got congruent term " << nn
                              << " from DB for " << n << std::endl;
        if (!nn.isNull())
        {
          ret = d_qstate.getRepresentative(nn);
          Trace("term-db-eval") << "return rep" << std::endl;
          ret_set = true;
          reqHasTerm = false;
          Assert(!ret.isNull());
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
    Kind rk = ret.getKind();
    if (rk != OR && rk != AND && rk != EQUAL && rk != ITE && rk != NOT
        && rk != FORALL)
    {
      if (!d_qstate.hasTerm(ret))
      {
        ret = Node::null();
      }
    }
  }
  Trace("term-db-eval") << "evaluated term : " << n << ", got : " << ret
                        << ", reqHasTerm = " << reqHasTerm << std::endl;
  visited[n] = ret;
  return ret;
}

TNode EntailmentCheck::getEntailedTerm2(TNode n,
                                        std::map<TNode, TNode>& subs,
                                        bool subsRep)
{
  Trace("term-db-entail") << "get entailed term : " << n << std::endl;
  if (d_qstate.hasTerm(n))
  {
    Trace("term-db-entail") << "...exists in ee, return rep " << std::endl;
    return n;
  }
  else if (n.getKind() == BOUND_VARIABLE)
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
      return getEntailedTerm2(it->second, subs, subsRep);
    }
  }
  else if (n.getKind() == ITE)
  {
    for (uint32_t i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], subs, subsRep, i == 0))
      {
        return getEntailedTerm2(n[i == 0 ? 1 : 2], subs, subsRep);
      }
    }
  }
  else
  {
    if (n.hasOperator())
    {
      TNode f = d_tdb.getMatchOperator(n);
      if (!f.isNull())
      {
        std::vector<TNode> args;
        for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
        {
          TNode c = getEntailedTerm2(n[i], subs, subsRep);
          if (c.isNull())
          {
            return TNode::null();
          }
          c = d_qstate.getRepresentative(c);
          Trace("term-db-entail") << "  child " << i << " : " << c << std::endl;
          args.push_back(c);
        }
        TNode nn = d_tdb.getCongruentTerm(f, args);
        Trace("term-db-entail")
            << "  got congruent term " << nn << " for " << n << std::endl;
        return nn;
      }
    }
  }
  return TNode::null();
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   std::map<TNode, TNode>& subs,
                                   bool subsRep,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  return evaluateTerm2(
      n, visited, subs, subsRep, useEntailmentTests, reqHasTerm);
}

Node EntailmentCheck::evaluateTerm(TNode n,
                                   bool useEntailmentTests,
                                   bool reqHasTerm)
{
  std::map<TNode, Node> visited;
  std::map<TNode, TNode> subs;
  return evaluateTerm2(n, visited, subs, false, useEntailmentTests, reqHasTerm);
}

TNode EntailmentCheck::getEntailedTerm(TNode n,
                                       std::map<TNode, TNode>& subs,
                                       bool subsRep)
{
  return getEntailedTerm2(n, subs, subsRep);
}

TNode EntailmentCheck::getEntailedTerm(TNode n)
{
  std::map<TNode, TNode> subs;
  return getEntailedTerm2(n, subs, false);
}

bool EntailmentCheck::isEntailed2(TNode n,
                                  std::map<TNode, TNode>& subs,
                                  bool subsRep,
                                  bool pol)
{
  Trace("term-db-entail") << "Check entailed : " << n << ", pol = " << pol
                          << std::endl;
  Assert(n.getType().isBoolean());
  Kind k = n.getKind();
  if (k == EQUAL && !n[0].getType().isBoolean())
  {
    TNode n1 = n[0].isConst() ? n[0] : getEntailedTerm2(n[0], subs, subsRep);
    if (!n1.isNull())
    {
      TNode n2 = n[1].isConst() ? n[1] : getEntailedTerm2(n[1], subs, subsRep);
      if (!n2.isNull())
      {
        if (pol)
        {
          // must check for equality here
          return d_qstate.areEqual(n1, n2);
        }
        return d_qstate.areDisequal(n1, n2);
      }
    }
  }
  else if (k == NOT)
  {
    return isEntailed2(n[0], subs, subsRep, !pol);
  }
  else if (k == OR || k == AND)
  {
    bool simPol = (pol && k == OR) || (!pol && k == AND);
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      if (isEntailed2(n[i], subs, subsRep, pol))
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
  else if (k == EQUAL || k == ITE)
  {
    Assert(n[0].getType().isBoolean());
    for (size_t i = 0; i < 2; i++)
    {
      if (isEntailed2(n[0], subs, subsRep, i == 0))
      {
        size_t ch = (k == EQUAL || i == 0) ? 1 : 2;
        bool reqPol = (k == ITE || i == 0) ? pol : !pol;
        return isEntailed2(n[ch], subs, subsRep, reqPol);
      }
    }
  }
  else if (k == FORALL)
  {
    if (!pol)
    {
      return isEntailed2(n[1], subs, subsRep, pol);
    }
  }
  else if (k == BOUND_VARIABLE || k == APPLY_UF)
  {
    // handles APPLY_UF, Boolean variable cases
    TNode n1 = getEntailedTerm2(n, subs, subsRep);
    if (!n1.isNull())
    {
      Assert(d_qstate.hasTerm(n1));
      n1 = d_qstate.getRepresentative(n1);
      if (n1.isConst())
      {
        return n1.getConst<bool>() == pol;
      }
    }
  }
  return false;
}

bool EntailmentCheck::isEntailed(TNode n, bool pol)
{
  std::map<TNode, TNode> subs;
  return isEntailed2(n, subs, false, pol);
}

bool EntailmentCheck::isEntailed(TNode n,
                                 std::map<TNode, TNode>& subs,
                                 bool subsRep,
                                 bool pol)
{
  return isEntailed2(n, subs, subsRep, pol);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

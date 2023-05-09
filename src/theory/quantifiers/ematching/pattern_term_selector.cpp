/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of pattern term selector class.
 */

#include "theory/quantifiers/ematching/pattern_term_selector.h"

#include "expr/node_algorithm.h"
#include "theory/arith/arith_msum.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

PatternTermSelector::PatternTermSelector(const Options& opts,
                                         Node q,
                                         options::TriggerSelMode tstrt,
                                         const std::vector<Node>& exc,
                                         bool filterInst)
    : d_opts(opts),
      d_quant(q),
      d_tstrt(tstrt),
      d_excluded(exc),
      d_filterInst(filterInst)
{
}

PatternTermSelector::~PatternTermSelector() {}

bool PatternTermSelector::isUsable(const Options& opts, Node n, Node q)
{
  if (quantifiers::TermUtil::getInstConstAttr(n) != q)
  {
    return true;
  }
  if (TriggerTermInfo::isAtomicTrigger(n))
  {
    for (const Node& nc : n)
    {
      if (!isUsable(opts, nc, q))
      {
        return false;
      }
    }
    return true;
  }
  else if (n.getKind() == INST_CONSTANT)
  {
    return true;
  }
  if (opts.quantifiers.purifyTriggers)
  {
    Node x = getInversionVariable(n);
    if (!x.isNull())
    {
      return true;
    }
  }
  return false;
}

Node PatternTermSelector::getIsUsableEq(const Options& opts, Node q, Node n)
{
  Assert(TriggerTermInfo::isRelationalTrigger(n));
  for (size_t i = 0; i < 2; i++)
  {
    if (isUsableEqTerms(opts, q, n[i], n[1 - i]))
    {
      if (i == 1 && n.getKind() == EQUAL
          && !quantifiers::TermUtil::hasInstConstAttr(n[0]))
      {
        return NodeManager::currentNM()->mkNode(EQUAL, n[1], n[0]);
      }
      else
      {
        return n;
      }
    }
  }
  return Node::null();
}

bool PatternTermSelector::isUsableEqTerms(const Options& opts,
                                          Node q,
                                          Node n1,
                                          Node n2)
{
  if (n1.getKind() == INST_CONSTANT)
  {
    if (opts.quantifiers.relationalTriggers)
    {
      Node q1 = quantifiers::TermUtil::getInstConstAttr(n1);
      if (q1 != q)
      {
        // x is a variable from another quantified formula, fail
        return false;
      }
      Node q2 = quantifiers::TermUtil::getInstConstAttr(n2);
      if (q2.isNull())
      {
        // x = c
        return true;
      }
      if (n2.getKind() == INST_CONSTANT && q2 == q)
      {
        // x = y
        return true;
      }
      // we dont check x = f(y), which is handled symmetrically below
      // when n1 and n2 are swapped
    }
  }
  else if (isUsableAtomicTrigger(opts, n1, q))
  {
    if (opts.quantifiers.relationalTriggers && n2.getKind() == INST_CONSTANT
        && quantifiers::TermUtil::getInstConstAttr(n2) == q
        && !expr::hasSubterm(n1, n2))
    {
      // f(x) = y
      return true;
    }
    else if (!quantifiers::TermUtil::hasInstConstAttr(n2))
    {
      // f(x) = c
      return true;
    }
  }
  return false;
}

Node PatternTermSelector::getIsUsableTrigger(const Options& opts,
                                             Node n,
                                             Node q)
{
  bool pol = true;
  Trace("trigger-debug") << "Is " << n << " a usable trigger?" << std::endl;
  if (n.getKind() == NOT)
  {
    pol = !pol;
    n = n[0];
  }
  NodeManager* nm = NodeManager::currentNM();
  if (n.getKind() == INST_CONSTANT)
  {
    return pol ? n : nm->mkNode(EQUAL, n, nm->mkConst(true)).notNode();
  }
  else if (TriggerTermInfo::isRelationalTrigger(n))
  {
    Node rtr = getIsUsableEq(opts, q, n);
    if (rtr.isNull() && n[0].getType().isRealOrInt())
    {
      // try to solve relation
      std::map<Node, Node> m;
      if (ArithMSum::getMonomialSumLit(n, m))
      {
        for (std::map<Node, Node>::iterator it = m.begin(); it != m.end(); ++it)
        {
          bool trySolve = false;
          if (!it->first.isNull())
          {
            if (it->first.getKind() == INST_CONSTANT)
            {
              trySolve = opts.quantifiers.relationalTriggers;
            }
            else if (isUsableTrigger(opts, it->first, q))
            {
              trySolve = true;
            }
          }
          if (trySolve)
          {
            Trace("trigger-debug")
                << "Try to solve for " << it->first << std::endl;
            Node veq;
            if (ArithMSum::isolate(it->first, m, veq, n.getKind()) != 0)
            {
              rtr = getIsUsableEq(opts, q, veq);
            }
            // either all solves will succeed or all solves will fail
            break;
          }
        }
      }
    }
    if (!rtr.isNull())
    {
      Trace("relational-trigger") << "Relational trigger : " << std::endl;
      Trace("relational-trigger")
          << "    " << rtr << " (from " << n << ")" << std::endl;
      Trace("relational-trigger") << "    in quantifier " << q << std::endl;
      Node rtr2 = pol ? rtr : rtr.negate();
      Trace("relational-trigger") << "    return : " << rtr2 << std::endl;
      return rtr2;
    }
    return Node::null();
  }
  Trace("trigger-debug") << n << " usable : "
                         << (quantifiers::TermUtil::getInstConstAttr(n) == q)
                         << " " << TriggerTermInfo::isAtomicTrigger(n) << " "
                         << isUsable(opts, n, q) << std::endl;
  if (isUsableAtomicTrigger(opts, n, q))
  {
    return pol ? n : nm->mkNode(EQUAL, n, nm->mkConst(true)).notNode();
  }
  return Node::null();
}

bool PatternTermSelector::isUsableAtomicTrigger(const Options& opts,
                                                Node n,
                                                Node q)
{
  return quantifiers::TermUtil::getInstConstAttr(n) == q
         && TriggerTermInfo::isAtomicTrigger(n) && isUsable(opts, n, q);
}

bool PatternTermSelector::isUsableTrigger(const Options& opts, Node n, Node q)
{
  Node nu = getIsUsableTrigger(opts, n, q);
  return !nu.isNull();
}

// store triggers in reqPol, indicating their polarity (if any) they must appear
// to falsify the quantified formula
void PatternTermSelector::collectTermsInternal(
    Node n,
    std::map<Node, std::vector<Node> >& visited,
    std::map<Node, TriggerTermInfo>& tinfo,
    options::TriggerSelMode tstrt,
    std::vector<Node>& added,
    bool pol,
    bool hasPol,
    bool epol,
    bool hasEPol,
    bool knowIsUsable)
{
  std::map<Node, std::vector<Node> >::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    // already visited
    for (const Node& t : itv->second)
    {
      if (std::find(added.begin(), added.end(), t) == added.end())
      {
        added.push_back(t);
      }
    }
    return;
  }
  visited[n].clear();
  Trace("auto-gen-trigger-debug2")
      << "Collect pat terms " << n << " " << pol << " " << hasPol << " " << epol
      << " " << hasEPol << std::endl;
  Kind nk = n.getKind();
  if (n.isClosure() || nk == INST_CONSTANT)
  {
    // do not traverse beneath quantified formulas
    return;
  }
  Node nu;
  bool nu_single = false;
  if (knowIsUsable)
  {
    nu = n;
  }
  else if (nk != NOT
           && std::find(d_excluded.begin(), d_excluded.end(), n)
                  == d_excluded.end())
  {
    nu = getIsUsableTrigger(d_opts, n, d_quant);
    if (!nu.isNull() && nu != n)
    {
      collectTermsInternal(
          nu, visited, tinfo, tstrt, added, pol, hasPol, epol, hasEPol, true);
      // copy to n
      visited[n].insert(visited[n].end(), added.begin(), added.end());
      return;
    }
  }
  if (!nu.isNull())
  {
    Assert(nu == n);
    Assert(nu.getKind() != NOT);
    Trace("auto-gen-trigger-debug2")
        << "...found usable trigger : " << nu << std::endl;
    Node reqEq;
    if (nu.getKind() == EQUAL)
    {
      if (TriggerTermInfo::isAtomicTrigger(nu[0])
          && !quantifiers::TermUtil::hasInstConstAttr(nu[1]))
      {
        if (hasPol)
        {
          reqEq = nu[1];
        }
        nu = nu[0];
      }
    }
    Assert(reqEq.isNull() || !quantifiers::TermUtil::hasInstConstAttr(reqEq));
    Assert(isUsableTrigger(d_opts, nu, d_quant));
    Trace("auto-gen-trigger-debug2")
        << "...add usable trigger : " << nu << std::endl;
    tinfo[nu].init(d_quant, nu, hasEPol ? (epol ? 1 : -1) : 0, reqEq);
    nu_single = tinfo[nu].d_fv.size() == d_quant[0].getNumChildren();
  }
  Node nrec = nu.isNull() ? n : nu;
  std::vector<Node> added2;
  for (size_t i = 0, nrecc = nrec.getNumChildren(); i < nrecc; i++)
  {
    bool newHasPol, newPol;
    bool newHasEPol, newEPol;
    QuantPhaseReq::getPolarity(nrec, i, hasPol, pol, newHasPol, newPol);
    QuantPhaseReq::getEntailPolarity(
        nrec, i, hasEPol, epol, newHasEPol, newEPol);
    collectTermsInternal(nrec[i],
                         visited,
                         tinfo,
                         tstrt,
                         added2,
                         newPol,
                         newHasPol,
                         newEPol,
                         newHasEPol);
  }
  // if this is not a usable trigger, don't worry about caching the results,
  // since triggers do not contain non-usable subterms
  if (nu.isNull())
  {
    return;
  }
  bool rm_nu = false;
  for (size_t i = 0, asize = added2.size(); i < asize; i++)
  {
    Trace("auto-gen-trigger-debug2") << "..." << nu << " added child " << i
                                     << " : " << added2[i] << std::endl;
    Assert(added2[i] != nu);
    // if child was not already removed
    if (tinfo.find(added2[i]) != tinfo.end())
    {
      if (tstrt == options::TriggerSelMode::MAX
          || (tstrt == options::TriggerSelMode::MIN_SINGLE_MAX && !nu_single))
      {
        // discard all subterms
        // do not remove if it has smaller weight
        if (tinfo[nu].d_weight <= tinfo[added2[i]].d_weight)
        {
          Trace("auto-gen-trigger-debug2") << "......remove it." << std::endl;
          visited[added2[i]].clear();
          tinfo.erase(added2[i]);
        }
      }
      else
      {
        if (tinfo[nu].d_fv.size() == tinfo[added2[i]].d_fv.size())
        {
          if (tinfo[nu].d_weight >= tinfo[added2[i]].d_weight)
          {
            // discard if we added a subterm as a trigger with all
            // variables that nu has
            Trace("auto-gen-trigger-debug2")
                << "......subsumes parent " << tinfo[nu].d_weight << " "
                << tinfo[added2[i]].d_weight << "." << std::endl;
            rm_nu = true;
          }
        }
        if (std::find(added.begin(), added.end(), added2[i]) == added.end())
        {
          added.push_back(added2[i]);
        }
      }
    }
  }
  if (rm_nu
      && (tstrt == options::TriggerSelMode::MIN
          || (tstrt == options::TriggerSelMode::MIN_SINGLE_ALL && nu_single)))
  {
    tinfo.erase(nu);
  }
  else
  {
    if (std::find(added.begin(), added.end(), nu) == added.end())
    {
      added.push_back(nu);
    }
  }
  visited[n].insert(visited[n].end(), added.begin(), added.end());
}

void PatternTermSelector::collect(Node n,
                                  std::vector<Node>& patTerms,
                                  std::map<Node, TriggerTermInfo>& tinfo)
{
  collectInternal(n, patTerms, tinfo, d_tstrt, d_filterInst);
}

void PatternTermSelector::collectInternal(
    Node n,
    std::vector<Node>& patTerms,
    std::map<Node, TriggerTermInfo>& tinfo,
    options::TriggerSelMode tstrt,
    bool filterInst)
{
  std::map<Node, std::vector<Node> > visited;
  if (filterInst)
  {
    // immediately do not consider any term t for which another term is an
    // instance of t
    std::vector<Node> patTerms2;
    std::map<Node, TriggerTermInfo> tinfo2;
    collectInternal(n, patTerms2, tinfo2, options::TriggerSelMode::ALL, false);
    std::vector<Node> temp;
    temp.insert(temp.begin(), patTerms2.begin(), patTerms2.end());
    filterInstances(temp);
    if (TraceIsOn("trigger-filter-instance"))
    {
      if (temp.size() != patTerms2.size())
      {
        Trace("trigger-filter-instance")
            << "Filtered an instance: " << std::endl;
        Trace("trigger-filter-instance") << "Old: ";
        for (unsigned i = 0; i < patTerms2.size(); i++)
        {
          Trace("trigger-filter-instance") << patTerms2[i] << " ";
        }
        Trace("trigger-filter-instance") << std::endl << "New: ";
        for (unsigned i = 0; i < temp.size(); i++)
        {
          Trace("trigger-filter-instance") << temp[i] << " ";
        }
        Trace("trigger-filter-instance") << std::endl;
      }
    }
    if (tstrt == options::TriggerSelMode::ALL)
    {
      for (const Node& t : temp)
      {
        // copy information
        tinfo[t].d_fv.insert(
            tinfo[t].d_fv.end(), tinfo2[t].d_fv.begin(), tinfo2[t].d_fv.end());
        tinfo[t].d_reqPol = tinfo2[t].d_reqPol;
        tinfo[t].d_reqPolEq = tinfo2[t].d_reqPolEq;
        patTerms.push_back(t);
      }
      return;
    }
    // do not consider terms that have instances
    for (const Node& t : patTerms2)
    {
      if (std::find(temp.begin(), temp.end(), t) == temp.end())
      {
        visited[t].clear();
      }
    }
  }
  std::vector<Node> added;
  collectTermsInternal(
      n, visited, tinfo, tstrt, added, true, true, false, true);
  for (const std::pair<const Node, TriggerTermInfo>& t : tinfo)
  {
    patTerms.push_back(t.first);
  }
}

int PatternTermSelector::isInstanceOf(Node n1,
                                      Node n2,
                                      const std::vector<Node>& fv1,
                                      const std::vector<Node>& fv2)
{
  Assert(n1 != n2);
  int status = 0;
  std::unordered_set<TNode> subs_vars;
  std::unordered_set<
      std::pair<TNode, TNode>,
      PairHashFunction<TNode, TNode, std::hash<TNode>, std::hash<TNode>>>
      visited;
  std::vector<std::pair<TNode, TNode> > visit;
  std::pair<TNode, TNode> cur;
  TNode cur1;
  TNode cur2;
  visit.push_back(std::pair<TNode, TNode>(n1, n2));
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) != visited.end())
    {
      continue;
    }
    visited.insert(cur);
    cur1 = cur.first;
    cur2 = cur.second;
    Assert(cur1 != cur2);
    // recurse if they have the same operator
    if (cur1.hasOperator() && cur2.hasOperator()
        && cur1.getNumChildren() == cur2.getNumChildren()
        && cur1.getOperator() == cur2.getOperator()
        && cur1.getOperator().getKind() != INST_CONSTANT)
    {
      visit.push_back(std::pair<TNode, TNode>(cur1, cur2));
      for (size_t i = 0, size = cur1.getNumChildren(); i < size; i++)
      {
        if (cur1[i] != cur2[i])
        {
          visit.push_back(std::pair<TNode, TNode>(cur1[i], cur2[i]));
        }
        else if (cur1[i].getKind() == INST_CONSTANT)
        {
          if (subs_vars.find(cur1[i]) != subs_vars.end())
          {
            return 0;
          }
          // the variable must map to itself in the substitution
          subs_vars.insert(cur1[i]);
        }
      }
      continue;
    }
    bool success = false;
    // check if we are in a unifiable instance case
    // must be only this case
    for (unsigned r = 0; r < 2; r++)
    {
      if (status == 0 || ((status == 1) == (r == 0)))
      {
        TNode curi = r == 0 ? cur1 : cur2;
        if (curi.getKind() == INST_CONSTANT
            && subs_vars.find(curi) == subs_vars.end())
        {
          TNode curj = r == 0 ? cur2 : cur1;
          // RHS must be a simple trigger
          if (TriggerTermInfo::getTriggerWeight(curj) == 0)
          {
            // must occur in the free variables in the other
            const std::vector<Node>& free_vars = r == 0 ? fv2 : fv1;
            if (std::find(free_vars.begin(), free_vars.end(), curi)
                != free_vars.end())
            {
              status = r == 0 ? 1 : -1;
              subs_vars.insert(curi);
              success = true;
              break;
            }
          }
        }
      }
    }
    if (!success)
    {
      return 0;
    }
  } while (!visit.empty());
  return status;
}

void PatternTermSelector::filterInstances(std::vector<Node>& nodes)
{
  std::map<unsigned, std::vector<Node> > fvs;
  for (size_t i = 0, size = nodes.size(); i < size; i++)
  {
    quantifiers::TermUtil::computeInstConstContains(nodes[i], fvs[i]);
  }
  std::vector<bool> active;
  active.resize(nodes.size(), true);
  for (size_t i = 0, size = nodes.size(); i < size; i++)
  {
    std::vector<Node>& fvsi = fvs[i];
    if (!active[i])
    {
      continue;
    }
    for (size_t j = i + 1, size2 = nodes.size(); j < size2; j++)
    {
      if (!active[j])
      {
        continue;
      }
      int result = isInstanceOf(nodes[i], nodes[j], fvsi, fvs[j]);
      if (result == 1)
      {
        Trace("filter-instances")
            << nodes[j] << " is an instance of " << nodes[i] << std::endl;
        active[i] = false;
        break;
      }
      else if (result == -1)
      {
        Trace("filter-instances")
            << nodes[i] << " is an instance of " << nodes[j] << std::endl;
        active[j] = false;
      }
    }
  }
  std::vector<Node> temp;
  for (size_t i = 0, nsize = nodes.size(); i < nsize; i++)
  {
    if (active[i])
    {
      temp.push_back(nodes[i]);
    }
  }
  nodes.clear();
  nodes.insert(nodes.begin(), temp.begin(), temp.end());
}

Node PatternTermSelector::getInversionVariable(Node n)
{
  Kind nk = n.getKind();
  if (nk == INST_CONSTANT)
  {
    return n;
  }
  else if (nk == ADD || nk == MULT)
  {
    Node ret;
    for (const Node& nc : n)
    {
      if (quantifiers::TermUtil::hasInstConstAttr(nc))
      {
        if (ret.isNull())
        {
          ret = getInversionVariable(nc);
          if (ret.isNull())
          {
            Trace("var-trigger-debug")
                << "No : multiple variables " << n << std::endl;
            return Node::null();
          }
        }
        else
        {
          return Node::null();
        }
      }
      else if (nk == MULT)
      {
        if (!nc.isConst())
        {
          Trace("var-trigger-debug")
              << "No : non-linear coefficient " << n << std::endl;
          return Node::null();
        }
      }
    }
    return ret;
  }
  Trace("var-trigger-debug")
      << "No : unsupported operator " << n << "." << std::endl;
  return Node::null();
}

Node PatternTermSelector::getInversion(Node n, Node x)
{
  Kind nk = n.getKind();
  if (nk == INST_CONSTANT)
  {
    return x;
  }
  else if (nk == ADD || nk == MULT)
  {
    NodeManager* nm = NodeManager::currentNM();
    int cindex = -1;
    bool cindexSet = false;
    for (size_t i = 0, nchild = n.getNumChildren(); i < nchild; i++)
    {
      Node nc = n[i];
      if (!quantifiers::TermUtil::hasInstConstAttr(nc))
      {
        if (nk == ADD)
        {
          x = nm->mkNode(SUB, x, nc);
        }
        else if (nk == MULT)
        {
          Assert(nc.isConst());
          if (x.getType().isInteger())
          {
            Node coeff = nm->mkConstInt(nc.getConst<Rational>().abs());
            if (!nc.getConst<Rational>().abs().isOne())
            {
              x = nm->mkNode(INTS_DIVISION_TOTAL, x, coeff);
            }
            if (nc.getConst<Rational>().sgn() < 0)
            {
              x = nm->mkNode(NEG, x);
            }
          }
          else
          {
            Node coeff = nm->mkConstReal(Rational(1) / nc.getConst<Rational>());
            x = nm->mkNode(MULT, x, coeff);
          }
        }
      }
      else
      {
        Assert(!cindexSet);
        cindex = i;
        cindexSet = true;
      }
    }
    if (cindexSet)
    {
      return getInversion(n[cindex], x);
    }
  }
  return Node::null();
}

void PatternTermSelector::getTriggerVariables(const Options& opts,
                                              Node n,
                                              Node q,
                                              std::vector<Node>& tvars)
{
  PatternTermSelector pts(opts, q, options::TriggerSelMode::ALL);
  std::vector<Node> patTerms;
  std::map<Node, TriggerTermInfo> tinfo;
  // collect all patterns from n
  pts.collect(n, patTerms, tinfo);
  // collect all variables from all patterns in patTerms, add to tvars
  for (const Node& pat : patTerms)
  {
    quantifiers::TermUtil::computeInstConstContainsForQuant(q, pat, tvars);
  }
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

/*********************                                                        */
/*! \file nl_monomial.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for monomials
 **/

#include "theory/arith/nl/nl_monomial.h"

#include "theory/arith/arith_utilities.h"
#include "theory/arith/nl/nl_lemma_utils.h"
#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {
namespace nl {

// Returns a[key] if key is in a or value otherwise.
unsigned getCountWithDefault(const NodeMultiset& a, Node key, unsigned value)
{
  NodeMultiset::const_iterator it = a.find(key);
  return (it == a.end()) ? value : it->second;
}
// Given two multisets return the multiset difference a \ b.
NodeMultiset diffMultiset(const NodeMultiset& a, const NodeMultiset& b)
{
  NodeMultiset difference;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a)
  {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value)
    {
      difference[key] = a_value - b_value;
    }
  }
  return difference;
}

// Return a vector containing a[key] repetitions of key in a multiset a.
std::vector<Node> ExpandMultiset(const NodeMultiset& a)
{
  std::vector<Node> expansion;
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a)
  {
    expansion.insert(expansion.end(), it_a->second, it_a->first);
  }
  return expansion;
}

// status 0 : n equal, -1 : n superset, 1 : n subset
void MonomialIndex::addTerm(Node n,
                            const std::vector<Node>& reps,
                            MonomialDb* nla,
                            int status,
                            unsigned argIndex)
{
  if (status == 0)
  {
    if (argIndex == reps.size())
    {
      d_monos.push_back(n);
    }
    else
    {
      d_data[reps[argIndex]].addTerm(n, reps, nla, status, argIndex + 1);
    }
  }
  for (std::map<Node, MonomialIndex>::iterator it = d_data.begin();
       it != d_data.end();
       ++it)
  {
    if (status != 0 || argIndex == reps.size() || it->first != reps[argIndex])
    {
      // if we do not contain this variable, then if we were a superset,
      // fail (-2), otherwise we are subset.  if we do contain this
      // variable, then if we were equal, we are superset since variables
      // are ordered, otherwise we remain the same.
      int new_status =
          std::find(reps.begin(), reps.end(), it->first) == reps.end()
              ? (status >= 0 ? 1 : -2)
              : (status == 0 ? -1 : status);
      if (new_status != -2)
      {
        it->second.addTerm(n, reps, nla, new_status, argIndex);
      }
    }
  }
  // compare for subsets
  for (unsigned i = 0; i < d_monos.size(); i++)
  {
    Node m = d_monos[i];
    if (m != n)
    {
      // we are superset if we are equal and haven't traversed all variables
      int cstatus = status == 0 ? (argIndex == reps.size() ? 0 : -1) : status;
      Trace("nl-ext-mindex-debug") << "  compare " << n << " and " << m
                                   << ", status = " << cstatus << std::endl;
      if (cstatus <= 0 && nla->isMonomialSubset(m, n))
      {
        nla->registerMonomialSubset(m, n);
        Trace("nl-ext-mindex-debug") << "...success" << std::endl;
      }
      else if (cstatus >= 0 && nla->isMonomialSubset(n, m))
      {
        nla->registerMonomialSubset(n, m);
        Trace("nl-ext-mindex-debug") << "...success (rev)" << std::endl;
      }
    }
  }
}

MonomialDb::MonomialDb()
{
  d_one = NodeManager::currentNM()->mkConst(Rational(1));
}

void MonomialDb::registerMonomial(Node n)
{
  if (std::find(d_monomials.begin(), d_monomials.end(), n) != d_monomials.end())
  {
    return;
  }
  d_monomials.push_back(n);
  Trace("nl-ext-debug") << "Register monomial : " << n << std::endl;
  Kind k = n.getKind();
  if (k == NONLINEAR_MULT)
  {
    // get exponent count
    unsigned nchild = n.getNumChildren();
    for (unsigned i = 0; i < nchild; i++)
    {
      d_m_exp[n][n[i]]++;
      if (i == 0 || n[i] != n[i - 1])
      {
        d_m_vlist[n].push_back(n[i]);
      }
    }
    d_m_degree[n] = nchild;
  }
  else if (n == d_one)
  {
    d_m_exp[n].clear();
    d_m_vlist[n].clear();
    d_m_degree[n] = 0;
  }
  else
  {
    Assert(k != PLUS && k != MULT);
    d_m_exp[n][n] = 1;
    d_m_vlist[n].push_back(n);
    d_m_degree[n] = 1;
  }
  std::sort(d_m_vlist[n].begin(), d_m_vlist[n].end());
  Trace("nl-ext-mindex") << "Add monomial to index : " << n << std::endl;
  d_m_index.addTerm(n, d_m_vlist[n], this);
}

void MonomialDb::registerMonomialSubset(Node a, Node b)
{
  Assert(isMonomialSubset(a, b));

  const NodeMultiset& a_exponent_map = getMonomialExponentMap(a);
  const NodeMultiset& b_exponent_map = getMonomialExponentMap(b);

  std::vector<Node> diff_children =
      ExpandMultiset(diffMultiset(b_exponent_map, a_exponent_map));
  Assert(!diff_children.empty());

  d_m_contain_parent[a].push_back(b);
  d_m_contain_children[b].push_back(a);

  Node mult_term = safeConstructNary(MULT, diff_children);
  Node nlmult_term = safeConstructNary(NONLINEAR_MULT, diff_children);
  d_m_contain_mult[a][b] = mult_term;
  d_m_contain_umult[a][b] = nlmult_term;
  Trace("nl-ext-mindex") << "..." << a << " is a subset of " << b
                         << ", difference is " << mult_term << std::endl;
}

bool MonomialDb::isMonomialSubset(Node am, Node bm) const
{
  const NodeMultiset& a = getMonomialExponentMap(am);
  const NodeMultiset& b = getMonomialExponentMap(bm);
  for (NodeMultiset::const_iterator it_a = a.begin(); it_a != a.end(); ++it_a)
  {
    Node key = it_a->first;
    const unsigned a_value = it_a->second;
    const unsigned b_value = getCountWithDefault(b, key, 0);
    if (a_value > b_value)
    {
      return false;
    }
  }
  return true;
}

const NodeMultiset& MonomialDb::getMonomialExponentMap(Node monomial) const
{
  MonomialExponentMap::const_iterator it = d_m_exp.find(monomial);
  Assert(it != d_m_exp.end());
  return it->second;
}

unsigned MonomialDb::getExponent(Node monomial, Node v) const
{
  MonomialExponentMap::const_iterator it = d_m_exp.find(monomial);
  if (it == d_m_exp.end())
  {
    return 0;
  }
  std::map<Node, unsigned>::const_iterator itv = it->second.find(v);
  if (itv == it->second.end())
  {
    return 0;
  }
  return itv->second;
}

const std::vector<Node>& MonomialDb::getVariableList(Node monomial) const
{
  std::map<Node, std::vector<Node> >::const_iterator itvl =
      d_m_vlist.find(monomial);
  Assert(itvl != d_m_vlist.end());
  return itvl->second;
}

unsigned MonomialDb::getDegree(Node monomial) const
{
  std::map<Node, unsigned>::const_iterator it = d_m_degree.find(monomial);
  Assert(it != d_m_degree.end());
  return it->second;
}

void MonomialDb::sortByDegree(std::vector<Node>& ms) const
{
  SortNonlinearDegree snlad(d_m_degree);
  std::sort(ms.begin(), ms.end(), snlad);
}

void MonomialDb::sortVariablesByModel(std::vector<Node>& ms, NlModel& m)
{
  SortNlModel smv;
  smv.d_nlm = &m;
  smv.d_isConcrete = false;
  smv.d_isAbsolute = true;
  smv.d_reverse_order = true;
  for (const Node& msc : ms)
  {
    std::sort(d_m_vlist[msc].begin(), d_m_vlist[msc].end(), smv);
  }
}

const std::map<Node, std::vector<Node> >& MonomialDb::getContainsChildrenMap()
{
  return d_m_contain_children;
}

const std::map<Node, std::vector<Node> >& MonomialDb::getContainsParentMap()
{
  return d_m_contain_parent;
}

Node MonomialDb::getContainsDiff(Node a, Node b) const
{
  std::map<Node, std::map<Node, Node> >::const_iterator it =
      d_m_contain_mult.find(a);
  if (it == d_m_contain_mult.end())
  {
    return Node::null();
  }
  std::map<Node, Node>::const_iterator it2 = it->second.find(b);
  if (it2 == it->second.end())
  {
    return Node::null();
  }
  return it2->second;
}

Node MonomialDb::getContainsDiffNl(Node a, Node b) const
{
  std::map<Node, std::map<Node, Node> >::const_iterator it =
      d_m_contain_umult.find(a);
  if (it == d_m_contain_umult.end())
  {
    return Node::null();
  }
  std::map<Node, Node>::const_iterator it2 = it->second.find(b);
  if (it2 == it->second.end())
  {
    return Node::null();
  }
  return it2->second;
}

Node MonomialDb::mkMonomialRemFactor(Node n,
                                     const NodeMultiset& n_exp_rem) const
{
  std::vector<Node> children;
  const NodeMultiset& exponent_map = getMonomialExponentMap(n);
  for (NodeMultiset::const_iterator itme2 = exponent_map.begin();
       itme2 != exponent_map.end();
       ++itme2)
  {
    Node v = itme2->first;
    unsigned inc = itme2->second;
    Trace("nl-ext-mono-factor")
        << "..." << inc << " factors of " << v << std::endl;
    unsigned count_in_n_exp_rem = getCountWithDefault(n_exp_rem, v, 0);
    Assert(count_in_n_exp_rem <= inc);
    inc -= count_in_n_exp_rem;
    Trace("nl-ext-mono-factor")
        << "......rem, now " << inc << " factors of " << v << std::endl;
    children.insert(children.end(), inc, v);
  }
  Node ret = safeConstructNary(MULT, children);
  ret = Rewriter::rewrite(ret);
  Trace("nl-ext-mono-factor") << "...return : " << ret << std::endl;
  return ret;
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace CVC4

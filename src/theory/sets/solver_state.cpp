/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sets state object.
 */

#include "theory/sets/solver_state.h"

#include "expr/emptyset.h"
#include "options/sets_options.h"
#include "theory/sets/theory_sets_private.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

SolverState::SolverState(Env& env, Valuation val, SkolemCache& skc)
    : TheoryState(env, val),
      d_skCache(skc),
      d_mapTerms(env.getUserContext()),
      d_groupTerms(env.getUserContext()),
      d_mapSkolemElements(env.getUserContext()),
      d_members(env.getContext()),
      d_partElementSkolems(env.getUserContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void SolverState::reset()
{
  d_set_eqc.clear();
  d_eqc_emptyset.clear();
  d_eqc_univset.clear();
  d_eqc_singleton.clear();
  d_congruent.clear();
  d_nvar_sets.clear();
  d_var_set.clear();
  d_compSets.clear();
  d_pol_mems[0].clear();
  d_pol_mems[1].clear();
  d_members_index.clear();
  d_singleton_index.clear();
  d_bop_index.clear();
  d_op_list.clear();
  d_allCompSets.clear();
  d_filterTerms.clear();
}

void SolverState::registerEqc(TypeNode tn, Node r)
{
  if (tn.isSet())
  {
    d_set_eqc.push_back(r);
  }
}

void SolverState::registerTerm(Node r, TypeNode tnn, Node n)
{
  Kind nk = n.getKind();
  if (nk == SET_MEMBER)
  {
    if (r.isConst())
    {
      Node s = d_ee->getRepresentative(n[1]);
      Node x = d_ee->getRepresentative(n[0]);
      int pindex = r == d_true ? 0 : (r == d_false ? 1 : -1);
      if (pindex != -1)
      {
        if (d_pol_mems[pindex][s].find(x) == d_pol_mems[pindex][s].end())
        {
          d_pol_mems[pindex][s][x] = n;
          Trace("sets-debug2") << "Membership[" << x << "][" << s << "] : " << n
                               << ", pindex = " << pindex << std::endl;
        }
        if (d_members_index[s].find(x) == d_members_index[s].end())
        {
          d_members_index[s][x] = n;
          d_op_list[SET_MEMBER].push_back(n);
        }
      }
      else
      {
        Assert(false);
      }
    }
  }
  else if (nk == SET_SINGLETON || nk == SET_UNION || nk == SET_INTER
           || nk == SET_MINUS || nk == SET_EMPTY || nk == SET_UNIVERSE)
  {
    if (nk == SET_SINGLETON)
    {
      Node re = d_ee->getRepresentative(n[0]);
      if (d_singleton_index.find(re) == d_singleton_index.end())
      {
        d_singleton_index[re] = n;
        d_eqc_singleton[r] = n;
        d_op_list[SET_SINGLETON].push_back(n);
      }
      else
      {
        d_congruent[n] = d_singleton_index[re];
      }
    }
    else if (nk == SET_EMPTY)
    {
      d_eqc_emptyset[tnn] = r;
    }
    else if (nk == SET_UNIVERSE)
    {
      Assert(options().sets.setsExt);
      d_eqc_univset[tnn] = r;
    }
    else
    {
      Node r1 = d_ee->getRepresentative(n[0]);
      Node r2 = d_ee->getRepresentative(n[1]);
      std::map<Node, Node>& binr1 = d_bop_index[nk][r1];
      std::map<Node, Node>::iterator itb = binr1.find(r2);
      if (itb == binr1.end())
      {
        binr1[r2] = n;
        d_op_list[nk].push_back(n);
      }
      else
      {
        d_congruent[n] = itb->second;
        // consider it regardless of whether congruent
        d_bop_index[nk][n[0]][n[1]] = n;
      }
    }
    d_nvar_sets[r].push_back(n);
    Trace("sets-debug2") << "Non-var-set[" << r << "] : " << n << std::endl;
  }
  else if (nk == SET_FILTER)
  {
    d_filterTerms.push_back(n);
  }
  else if (nk == SET_MAP)
  {
    d_mapTerms.insert(n);
    if (d_mapSkolemElements.find(n) == d_mapSkolemElements.end())
    {
      std::shared_ptr<context::CDHashSet<Node>> set =
          std::make_shared<context::CDHashSet<Node>>(d_env.getUserContext());
      d_mapSkolemElements[n] = set;
    }
  }
  else if (nk == RELATION_GROUP)
  {
    d_groupTerms.insert(n);
    std::shared_ptr<context::CDHashSet<Node>> set =
        std::make_shared<context::CDHashSet<Node>>(d_env.getUserContext());
    d_partElementSkolems[n] = set;
  }
  else if (nk == SET_COMPREHENSION)
  {
    d_compSets[r].push_back(n);
    d_allCompSets.push_back(n);
    Trace("sets-debug2") << "Comp-set[" << r << "] : " << n << std::endl;
  }
  else if (Theory::isLeafOf(n, THEORY_SETS) && !d_skCache.isSkolem(n))
  {
    // It is important that we check it is a leaf, due to parametric theories
    // that may be used to construct terms of set type. It is also important to
    // exclude internally introduced skolems, due to the semantics of the
    // universe set.
    if (tnn.isSet())
    {
      if (d_var_set.find(r) == d_var_set.end())
      {
        d_var_set[r] = n;
        Trace("sets-debug2") << "var-set[" << r << "] : " << n << std::endl;
      }
    }
  }
  else
  {
    Trace("sets-debug2") << "Unknown-set[" << r << "] : " << n << std::endl;
  }
}

void SolverState::addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const
{
  if (a != b)
  {
    Assert(areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
}

Node SolverState::getEmptySetEqClass(TypeNode tn) const
{
  std::map<TypeNode, Node>::const_iterator it = d_eqc_emptyset.find(tn);
  if (it != d_eqc_emptyset.end())
  {
    return it->second;
  }
  return Node::null();
}

Node SolverState::getUnivSetEqClass(TypeNode tn) const
{
  std::map<TypeNode, Node>::const_iterator it = d_eqc_univset.find(tn);
  if (it != d_eqc_univset.end())
  {
    return it->second;
  }
  return Node::null();
}

Node SolverState::getSingletonEqClass(Node r) const
{
  std::map<Node, Node>::const_iterator it = d_eqc_singleton.find(r);
  if (it != d_eqc_singleton.end())
  {
    return it->second;
  }
  return Node::null();
}

Node SolverState::getBinaryOpTerm(Kind k, Node r1, Node r2) const
{
  std::map<Kind, std::map<Node, std::map<Node, Node> > >::const_iterator itk =
      d_bop_index.find(k);
  if (itk == d_bop_index.end())
  {
    return Node::null();
  }
  std::map<Node, std::map<Node, Node> >::const_iterator it1 =
      itk->second.find(r1);
  if (it1 == itk->second.end())
  {
    return Node::null();
  }
  std::map<Node, Node>::const_iterator it2 = it1->second.find(r2);
  if (it2 == it1->second.end())
  {
    return Node::null();
  }
  return it2->second;
}

bool SolverState::isEntailed(Node n, bool polarity) const
{
  if (n.getKind() == NOT)
  {
    return isEntailed(n[0], !polarity);
  }
  else if (n.getKind() == EQUAL)
  {
    if (polarity)
    {
      return areEqual(n[0], n[1]);
    }
    return areDisequal(n[0], n[1]);
  }
  else if (n.getKind() == SET_MEMBER)
  {
    if (areEqual(n, polarity ? d_true : d_false))
    {
      return true;
    }
    // check members cache
    if (polarity && d_ee->hasTerm(n[1]))
    {
      Node r = d_ee->getRepresentative(n[1]);
      if (isMember(n[0], r))
      {
        return true;
      }
    }
  }
  else if (n.getKind() == AND || n.getKind() == OR)
  {
    bool conj = (n.getKind() == AND) == polarity;
    for (const Node& nc : n)
    {
      bool isEnt = isEntailed(nc, polarity);
      if (isEnt != conj)
      {
        return !conj;
      }
    }
    return conj;
  }
  else if (n.isConst())
  {
    return (polarity && n == d_true) || (!polarity && n == d_false);
  }
  return false;
}

bool SolverState::isSetDisequalityEntailed(Node r1, Node r2) const
{
  Assert(d_ee->hasTerm(r1) && d_ee->getRepresentative(r1) == r1);
  Assert(d_ee->hasTerm(r2) && d_ee->getRepresentative(r2) == r2);
  TypeNode tn = r1.getType();
  Node re = getEmptySetEqClass(tn);
  for (unsigned e = 0; e < 2; e++)
  {
    Node a = e == 0 ? r1 : r2;
    Node b = e == 0 ? r2 : r1;
    if (isSetDisequalityEntailedInternal(a, b, re))
    {
      return true;
    }
  }
  return false;
}

bool SolverState::isSetDisequalityEntailedInternal(Node a,
                                                   Node b,
                                                   Node re) const
{
  // if there are members in a
  std::map<Node, std::map<Node, Node> >::const_iterator itpma =
      d_pol_mems[0].find(a);
  if (itpma == d_pol_mems[0].end())
  {
    // no positive members, continue
    return false;
  }
  // if b is empty
  if (b == re)
  {
    if (!itpma->second.empty())
    {
      Trace("sets-deq") << "Disequality is satisfied because members are in "
                        << a << " and " << b << " is empty" << std::endl;
      return true;
    }
    else
    {
      // a should not be singleton
      Assert(d_eqc_singleton.find(a) == d_eqc_singleton.end());
    }
    return false;
  }
  std::map<Node, Node>::const_iterator itsb = d_eqc_singleton.find(b);
  std::map<Node, std::map<Node, Node> >::const_iterator itpmb =
      d_pol_mems[1].find(b);
  std::vector<Node> prev;
  for (const std::pair<const Node, Node>& itm : itpma->second)
  {
    // if b is a singleton
    if (itsb != d_eqc_singleton.end())
    {
      if (areDisequal(itm.first, itsb->second[0]))
      {
        Trace("sets-deq") << "Disequality is satisfied because of "
                          << itm.second << ", singleton eq " << itsb->second[0]
                          << std::endl;
        return true;
      }
      // or disequal with another member
      for (const Node& p : prev)
      {
        if (areDisequal(itm.first, p))
        {
          Trace("sets-deq")
              << "Disequality is satisfied because of disequal members "
              << itm.first << " " << p << ", singleton eq " << std::endl;
          return true;
        }
      }
      // if a has positive member that is negative member in b
    }
    else if (itpmb != d_pol_mems[1].end())
    {
      for (const std::pair<const Node, Node>& itnm : itpmb->second)
      {
        if (areEqual(itm.first, itnm.first))
        {
          Trace("sets-deq") << "Disequality is satisfied because of "
                            << itm.second << " " << itnm.second << std::endl;
          return true;
        }
      }
    }
    prev.push_back(itm.first);
  }
  return false;
}

Node SolverState::getCongruent(Node n) const
{
  Assert(d_ee->hasTerm(n));
  std::map<Node, Node>::const_iterator it = d_congruent.find(n);
  if (it == d_congruent.end())
  {
    return n;
  }
  return it->second;
}
bool SolverState::isCongruent(Node n) const
{
  return d_congruent.find(n) != d_congruent.end();
}
const std::vector<Node>& SolverState::getNonVariableSets(Node r) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_nvar_sets.find(r);
  if (it == d_nvar_sets.end())
  {
    return d_emptyVec;
  }
  return it->second;
}

Node SolverState::getVariableSet(Node r) const
{
  std::map<Node, Node>::const_iterator it = d_var_set.find(r);
  if (it != d_var_set.end())
  {
    return it->second;
  }
  return Node::null();
}

const std::vector<Node>& SolverState::getComprehensionSets(Node r) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_compSets.find(r);
  if (it == d_compSets.end())
  {
    return d_emptyVec;
  }
  return it->second;
}

const std::map<Node, Node>& SolverState::getMembers(Node r) const
{
  Assert(r == getRepresentative(r));
  return getMembersInternal(r, 0);
}
const std::map<Node, Node>& SolverState::getNegativeMembers(Node r) const
{
  Assert(r == getRepresentative(r));
  return getMembersInternal(r, 1);
}
const std::map<Node, Node>& SolverState::getMembersInternal(Node r,
                                                            unsigned i) const
{
  std::map<Node, std::map<Node, Node> >::const_iterator itp =
      d_pol_mems[i].find(r);
  if (itp == d_pol_mems[i].end())
  {
    return d_emptyMap;
  }
  return itp->second;
}

bool SolverState::hasMembers(Node r) const
{
  std::map<Node, std::map<Node, Node> >::const_iterator it =
      d_pol_mems[0].find(r);
  if (it == d_pol_mems[0].end())
  {
    return false;
  }
  return !it->second.empty();
}
const std::map<Kind, std::map<Node, std::map<Node, Node> > >&
SolverState::getBinaryOpIndex() const
{
  return d_bop_index;
}

const std::map<Node, std::map<Node, Node>>& SolverState::getBinaryOpIndex(
    Kind k)
{
  return d_bop_index[k];
}

const std::map<Kind, std::vector<Node> >& SolverState::getOperatorList() const
{
  return d_op_list;
}

const std::vector<Node>& SolverState::getFilterTerms() const { return d_filterTerms; }

const context::CDHashSet<Node>& SolverState::getMapTerms() const { return d_mapTerms; }

const context::CDHashSet<Node>& SolverState::getGroupTerms() const
{
  return d_groupTerms;
}

std::shared_ptr<context::CDHashSet<Node>> SolverState::getMapSkolemElements(
    Node n)
{
  return d_mapSkolemElements[n];
}

const std::vector<Node>& SolverState::getComprehensionSets() const
{
  return d_allCompSets;
}

const vector<Node> SolverState::getSetsEqClasses(const TypeNode& t) const
{
  vector<Node> representatives;
  for (const Node& eqc : getSetsEqClasses())
  {
    if (eqc.getType().getSetElementType() == t)
    {
      representatives.push_back(eqc);
    }
  }
  return representatives;
}

bool SolverState::isMember(TNode x, TNode s) const
{
  Assert(hasTerm(s) && getRepresentative(s) == s);
  NodeIntMap::const_iterator mem_i = d_members.find(s);
  if (mem_i != d_members.end())
  {
    std::map<Node, std::vector<Node> >::const_iterator itd =
        d_members_data.find(s);
    Assert(itd != d_members_data.end());
    const std::vector<Node>& members = itd->second;
    Assert((*mem_i).second <= members.size());
    for (size_t i = 0, nmem = (*mem_i).second; i < nmem; i++)
    {
      if (areEqual(members[i][0], x))
      {
        return true;
      }
    }
  }
  return false;
}

void SolverState::addMember(TNode r, TNode atom)
{
  NodeIntMap::iterator mem_i = d_members.find(r);
  size_t n_members = 0;
  if (mem_i != d_members.end())
  {
    n_members = (*mem_i).second;
  }
  d_members[r] = n_members + 1;
  if (n_members < d_members_data[r].size())
  {
    d_members_data[r][n_members] = atom;
  }
  else
  {
    d_members_data[r].push_back(atom);
  }
}

bool SolverState::merge(TNode t1,
                        TNode t2,
                        std::vector<Node>& facts,
                        TNode cset)
{
  NodeIntMap::iterator mem_i2 = d_members.find(t2);
  if (mem_i2 == d_members.end())
  {
    // no members in t2, we are done
    return true;
  }
  NodeIntMap::iterator mem_i1 = d_members.find(t1);
  size_t n_members = 0;
  if (mem_i1 != d_members.end())
  {
    n_members = (*mem_i1).second;
  }
  for (size_t i = 0, nmem2 = (*mem_i2).second; i < nmem2; i++)
  {
    Assert(i < d_members_data[t2].size()
           && d_members_data[t2][i].getKind() == SET_MEMBER);
    Node m2 = d_members_data[t2][i];
    // check if redundant
    bool add = true;
    for (size_t j = 0; j < n_members; j++)
    {
      Assert(j < d_members_data[t1].size()
             && d_members_data[t1][j].getKind() == SET_MEMBER);
      if (areEqual(m2[0], d_members_data[t1][j][0]))
      {
        add = false;
        break;
      }
    }
    if (add)
    {
      // if there is a concrete set in t1, propagate new facts or conflicts
      if (!cset.isNull())
      {
        NodeManager* nm = NodeManager::currentNM();
        Assert(areEqual(m2[1], cset));
        Node exp = nm->mkNode(AND, m2[1].eqNode(cset), m2);
        if (cset.getKind() == SET_SINGLETON)
        {
          if (cset[0] != m2[0])
          {
            Node eq = cset[0].eqNode(m2[0]);
            Trace("sets-prop") << "Propagate eq-mem eq inference : " << exp
                               << " => " << eq << std::endl;
            Node fact = nm->mkNode(IMPLIES, exp, eq);
            facts.push_back(fact);
          }
        }
        else
        {
          // conflict
          Assert(facts.empty());
          Trace("sets-prop")
              << "Propagate eq-mem conflict : " << exp << std::endl;
          facts.push_back(exp);
          return false;
        }
      }
      if (n_members < d_members_data[t1].size())
      {
        d_members_data[t1][n_members] = m2;
      }
      else
      {
        d_members_data[t1].push_back(m2);
      }
      n_members++;
    }
  }
  d_members[t1] = n_members;
  return true;
}

void SolverState::registerMapSkolemElement(const Node& n, const Node& element)
{
  Assert(n.getKind() == kind::SET_MAP);
  Assert(element.getKind() == SKOLEM
         && element.getType() == n[1].getType().getSetElementType());
  d_mapSkolemElements[n].get()->insert(element);
}

void SolverState::registerPartElementSkolem(Node group, Node skolemElement)
{
  Assert(group.getKind() == RELATION_GROUP);
  Assert(skolemElement.getType() == group[0].getType().getSetElementType());
  d_partElementSkolems[group].get()->insert(skolemElement);
}

std::shared_ptr<context::CDHashSet<Node>> SolverState::getPartElementSkolems(
    Node n)
{
  Assert(n.getKind() == RELATION_GROUP);
  return d_partElementSkolems[n];
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

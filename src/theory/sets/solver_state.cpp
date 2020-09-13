/*********************                                                        */
/*! \file solver_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sets state object
 **/

#include "theory/sets/solver_state.h"

#include "expr/emptyset.h"
#include "options/sets_options.h"
#include "theory/sets/theory_sets_private.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

SolverState::SolverState(context::Context* c,
                         context::UserContext* u,
                         Valuation val,
                         SkolemCache& skc)
    : TheoryState(c, u, val), d_skCache(skc), d_parent(nullptr)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void SolverState::setParent(TheorySetsPrivate* p) { d_parent = p; }

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
  if (nk == MEMBER)
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
          d_op_list[MEMBER].push_back(n);
        }
      }
      else
      {
        Assert(false);
      }
    }
  }
  else if (nk == SINGLETON || nk == UNION || nk == INTERSECTION
           || nk == SETMINUS || nk == EMPTYSET || nk == UNIVERSE_SET)
  {
    if (nk == SINGLETON)
    {
      Node re = d_ee->getRepresentative(n[0]);
      if (d_singleton_index.find(re) == d_singleton_index.end())
      {
        d_singleton_index[re] = n;
        d_eqc_singleton[r] = n;
        d_op_list[SINGLETON].push_back(n);
      }
      else
      {
        d_congruent[n] = d_singleton_index[re];
      }
    }
    else if (nk == EMPTYSET)
    {
      d_eqc_emptyset[tnn] = r;
    }
    else if (nk == UNIVERSE_SET)
    {
      Assert(options::setsExt());
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
      }
    }
    d_nvar_sets[r].push_back(n);
    Trace("sets-debug2") << "Non-var-set[" << r << "] : " << n << std::endl;
  }
  else if (nk == COMPREHENSION)
  {
    d_compSets[r].push_back(n);
    d_allCompSets.push_back(n);
    Trace("sets-debug2") << "Comp-set[" << r << "] : " << n << std::endl;
  }
  else if (n.isVar() && !d_skCache.isSkolem(n))
  {
    // it is important that we check it is a variable, but not an internally
    // introduced skolem, due to the semantics of the universe set.
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
  else if (n.getKind() == MEMBER)
  {
    if (areEqual(n, polarity ? d_true : d_false))
    {
      return true;
    }
    // check members cache
    if (polarity && d_ee->hasTerm(n[1]))
    {
      Node r = d_ee->getRepresentative(n[1]);
      if (d_parent->isMember(n[0], r))
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
  return getMembersInternal(r, 0);
}
const std::map<Node, Node>& SolverState::getNegativeMembers(Node r) const
{
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
const std::map<Kind, std::vector<Node> >& SolverState::getOperatorList() const
{
  return d_op_list;
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

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

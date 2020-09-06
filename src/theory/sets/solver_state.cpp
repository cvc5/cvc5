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
                         Valuation val)
    : TheoryState(c, u, val), d_parent(nullptr), d_proxy(u), d_proxy_to_term(u)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void SolverState::reset()
{
  d_pol_mems[0].clear();
  d_pol_mems[1].clear();
}

void SolverState::registerTerm(Node r, TypeNode tnn, Node n)
{
  // FIXME
}

void SolverState::addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const
{
  if (a != b)
  {
    Assert(areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
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

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

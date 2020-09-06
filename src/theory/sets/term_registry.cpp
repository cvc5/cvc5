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

TermRegistry::TermRegistry(olverState& state, InferenceManager& im)
    : d_state(state), d_im(im), d_proxy(state.getUserContext()), d_proxy_to_term(state.getUserContext())
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}

void TermRegistry::setParent(TheorySetsPrivate* p) { d_parent = p; }

void TermRegistry::reset()
{
  d_set_eqc.clear();
  d_eqc_emptyset.clear();
  d_eqc_univset.clear();
  d_eqc_singleton.clear();
  d_congruent.clear();
  d_nvar_sets.clear();
  d_var_set.clear();
  d_compSets.clear();
  d_members_index.clear();
  d_singleton_index.clear();
  d_bop_index.clear();
  d_op_list.clear();
  d_allCompSets.clear();
}

void TermRegistry::registerEqc(TypeNode tn, Node r)
{
  if (tn.isSet())
  {
    d_set_eqc.push_back(r);
  }
}

void TermRegistry::registerTerm(Node r, TypeNode tnn, Node n)
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
      // singleton lemma
      getProxy(n);
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

void TermRegistry::addEqualityToExp(Node a, Node b, std::vector<Node>& exp) const
{
  if (a != b)
  {
    Assert(areEqual(a, b));
    exp.push_back(a.eqNode(b));
  }
}

Node TermRegistry::getEmptySetEqClass(TypeNode tn) const
{
  std::map<TypeNode, Node>::const_iterator it = d_eqc_emptyset.find(tn);
  if (it != d_eqc_emptyset.end())
  {
    return it->second;
  }
  return Node::null();
}

Node TermRegistry::getUnivSetEqClass(TypeNode tn) const
{
  std::map<TypeNode, Node>::const_iterator it = d_univset.find(tn);
  if (it != d_univset.end())
  {
    return it->second;
  }
  return Node::null();
}

Node TermRegistry::getSingletonEqClass(Node r) const
{
  std::map<Node, Node>::const_iterator it = d_eqc_singleton.find(r);
  if (it != d_eqc_singleton.end())
  {
    return it->second;
  }
  return Node::null();
}

Node TermRegistry::getBinaryOpTerm(Kind k, Node r1, Node r2) const
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

bool TermRegistry::isEntailed(Node n, bool polarity) const
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

Node TermRegistry::getProxy(Node n)
{
  Kind nk = n.getKind();
  if (nk != EMPTYSET && nk != SINGLETON && nk != INTERSECTION && nk != SETMINUS
      && nk != UNION && nk != UNIVERSE_SET)
  {
    return n;
  }
  NodeMap::const_iterator it = d_proxy.find(n);
  if (it != d_proxy.end())
  {
    return (*it).second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node k = d_skCache.mkTypedSkolemCached(
      n.getType(), n, SkolemCache::SK_PURIFY, "sp");
  d_proxy[n] = k;
  d_proxy_to_term[k] = n;
  Node eq = k.eqNode(n);
  Trace("sets-lemma") << "Sets::Lemma : " << eq << " by proxy" << std::endl;
  d_parent->getOutputChannel()->lemma(eq);
  if (nk == SINGLETON)
  {
    Node slem = nm->mkNode(MEMBER, n[0], k);
    Trace("sets-lemma") << "Sets::Lemma : " << slem << " by singleton"
                        << std::endl;
    d_parent->getOutputChannel()->lemma(slem);
  }
  return k;
}

Node TermRegistry::getCongruent(Node n) const
{
  Assert(d_ee->hasTerm(n));
  std::map<Node, Node>::const_iterator it = d_congruent.find(n);
  if (it == d_congruent.end())
  {
    return n;
  }
  return it->second;
}
bool TermRegistry::isCongruent(Node n) const
{
  return d_congruent.find(n) != d_congruent.end();
}

Node TermRegistry::getEmptySet(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_emptyset.find(tn);
  if (it != d_emptyset.end())
  {
    return it->second;
  }
  Node n = NodeManager::currentNM()->mkConst(EmptySet(tn));
  d_emptyset[tn] = n;
  return n;
}
Node TermRegistry::getUnivSet(TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_univset.find(tn);
  if (it != d_univset.end())
  {
    return it->second;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node n = nm->mkNullaryOperator(tn, UNIVERSE_SET);
  for (it = d_univset.begin(); it != d_univset.end(); ++it)
  {
    Node n1;
    Node n2;
    if (tn.isSubtypeOf(it->first))
    {
      n1 = n;
      n2 = it->second;
    }
    else if (it->first.isSubtypeOf(tn))
    {
      n1 = it->second;
      n2 = n;
    }
    if (!n1.isNull())
    {
      Node ulem = nm->mkNode(SUBSET, n1, n2);
      Trace("sets-lemma") << "Sets::Lemma : " << ulem << " by univ-type"
                          << std::endl;
      d_parent->getOutputChannel()->lemma(ulem);
    }
  }
  d_univset[tn] = n;
  return n;
}

Node TermRegistry::getTypeConstraintSkolem(Node n, TypeNode tn)
{
  std::map<TypeNode, Node>::iterator it = d_tc_skolem[n].find(tn);
  if (it == d_tc_skolem[n].end())
  {
    Node k = NodeManager::currentNM()->mkSkolem("tc_k", tn);
    d_tc_skolem[n][tn] = k;
    return k;
  }
  return it->second;
}

const std::vector<Node>& TermRegistry::getNonVariableSets(Node r) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_nvar_sets.find(r);
  if (it == d_nvar_sets.end())
  {
    return d_emptyVec;
  }
  return it->second;
}

Node TermRegistry::getVariableSet(Node r) const
{
  std::map<Node, Node>::const_iterator it = d_var_set.find(r);
  if (it != d_var_set.end())
  {
    return it->second;
  }
  return Node::null();
}

const std::vector<Node>& TermRegistry::getComprehensionSets(Node r) const
{
  std::map<Node, std::vector<Node> >::const_iterator it = d_compSets.find(r);
  if (it == d_compSets.end())
  {
    return d_emptyVec;
  }
  return it->second;
}

const std::map<Kind, std::map<Node, std::map<Node, Node> > >&
TermRegistry::getBinaryOpIndex() const
{
  return d_bop_index;
}
const std::map<Kind, std::vector<Node> >& TermRegistry::getOperatorList() const
{
  return d_op_list;
}

const std::vector<Node>& TermRegistry::getComprehensionSets() const
{
  return d_allCompSets;
}

void TermRegistry::debugPrintSet(Node s, const char* c) const
{
  if (s.getNumChildren() == 0)
  {
    NodeMap::const_iterator it = d_proxy_to_term.find(s);
    if (it != d_proxy_to_term.end())
    {
      debugPrintSet((*it).second, c);
    }
    else
    {
      Trace(c) << s;
    }
  }
  else
  {
    Trace(c) << "(" << s.getOperator();
    for (const Node& sc : s)
    {
      Trace(c) << " ";
      debugPrintSet(sc, c);
    }
    Trace(c) << ")";
  }
}

const vector<Node> TermRegistry::getSetsEqClasses(const TypeNode& t) const
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

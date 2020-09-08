/*********************                                                        */
/*! \file term_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of sets term registry object
 **/

#include "theory/sets/term_registry.h"

#include "expr/emptyset.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace sets {

TermRegistry::TermRegistry(SolverState& state,
                           InferenceManager& im,
                           SkolemCache& skc)
    : d_im(im),
      d_skCache(skc),
      d_proxy(state.getUserContext()),
      d_proxy_to_term(state.getUserContext())
{
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
  d_im.lemma(eq, LemmaProperty::NONE, false);
  if (nk == SINGLETON)
  {
    Node slem = nm->mkNode(MEMBER, n[0], k);
    Trace("sets-lemma") << "Sets::Lemma : " << slem << " by singleton"
                        << std::endl;
    d_im.lemma(slem, LemmaProperty::NONE, false);
  }
  return k;
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
      d_im.lemma(ulem, LemmaProperty::NONE, false);
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

}  // namespace sets
}  // namespace theory
}  // namespace CVC4

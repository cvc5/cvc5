/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sets term registry object.
 */

#include "theory/sets/term_registry.h"

#include "expr/emptyset.h"
#include "expr/skolem_manager.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace sets {

TermRegistry::TermRegistry(Env& env,
                           SolverState& state,
                           InferenceManager& im,
                           SkolemCache& skc)
    : EnvObj(env),
      d_im(im),
      d_skCache(skc),
      d_proxy(userContext()),
      d_proxy_to_term(userContext()),
      d_epg(env.isTheoryProofProducing() ? new EagerProofGenerator(
                env, nullptr, "sets::TermRegistry::epg")
                                         : nullptr)
{
}

Node TermRegistry::getProxy(Node n)
{
  Kind nk = n.getKind();
  if (nk != SET_EMPTY && nk != SET_SINGLETON && nk != SET_INTER
      && nk != SET_MINUS && nk != SET_UNION && nk != SET_UNIVERSE
      && nk != SET_MAP)
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
  sendSimpleLemmaInternal(eq, InferenceId::SETS_PROXY);
  if (nk == SET_SINGLETON)
  {
    Node slem = nm->mkNode(SET_MEMBER, n[0], k);
    sendSimpleLemmaInternal(slem, InferenceId::SETS_PROXY_SINGLETON);
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
  Node n = nm->mkNullaryOperator(tn, SET_UNIVERSE);
  d_univset[tn] = n;
  return n;
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

void TermRegistry::sendSimpleLemmaInternal(Node n, InferenceId id)
{
  Trace("sets-lemma") << "Sets::Lemma : " << n << " by " << id << std::endl;
  if (d_epg.get() != nullptr)
  {
    TrustNode teq =
        d_epg->mkTrustNode(n, PfRule::MACRO_SR_PRED_INTRO, {}, {n});
    d_im.trustedLemma(teq, id);
  }
  else
  {
    d_im.lemma(n, id);
  }
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

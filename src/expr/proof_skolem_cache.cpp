/*********************                                                        */
/*! \file proof_skolem_cache.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof skolem cache
 **/

#include "expr/proof_skolem_cache.h"

#include "expr/attribute.h"

using namespace CVC4::kind;

namespace CVC4 {

struct WitnessFormAttributeId
{
};
typedef expr::Attribute<WitnessFormAttributeId, Node> WitnessFormAttribute;

struct SkolemFormAttributeId
{
};
typedef expr::Attribute<SkolemFormAttributeId, Node> SkolemFormAttribute;

struct PurifySkolemAttributeId
{
};
typedef expr::Attribute<PurifySkolemAttributeId, Node> PurifySkolemAttribute;

Node ProofSkolemCache::mkSkolem(Node v,
                                Node pred,
                                const std::string& prefix,
                                const std::string& comment,
                                int flags)
{
  Assert(v.getKind() == BOUND_VARIABLE);
  // make the witness term
  NodeManager* nm = NodeManager::currentNM();
  Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
  // translate pred to witness form, since pred itself may contain skolem
  Node predw = getWitnessForm(pred);
  // make the witness term, which should not contain any skolem
  Node w = nm->mkNode(WITNESS, bvl, predw);
  return getOrMakeSkolem(w, prefix, comment, flags);
}

Node ProofSkolemCache::mkSkolemExists(Node v,
                                      Node q,
                                      const std::string& prefix,
                                      const std::string& comment,
                                      int flags)
{
  Assert(q.getKind() == EXISTS);
  bool foundVar = false;
  std::vector<Node> ovars;
  for (const Node& av : q[0])
  {
    if (av == v)
    {
      foundVar = true;
      continue;
    }
    ovars.push_back(av);
  }
  if (!foundVar)
  {
    Assert(false);
    return Node::null();
  }
  Node pred = q[1];
  if (!ovars.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node bvl = nm->mkNode(BOUND_VAR_LIST, ovars);
    pred = nm->mkNode(EXISTS, bvl, pred);
  }
  return mkSkolem(v, pred, prefix, comment, flags);
}

Node ProofSkolemCache::mkPurifySkolem(Node t,
                                      const std::string& prefix,
                                      const std::string& comment,
                                      int flags)
{
  PurifySkolemAttribute psa;
  if (t.hasAttribute(psa))
  {
    return t.getAttribute(psa);
  }
  // The case where t is a witness term is special: we set its Skolem attribute
  // directly.
  if (t.getKind() == WITNESS)
  {
    return getOrMakeSkolem(t, prefix, comment, flags);
  }
  Node v = NodeManager::currentNM()->mkBoundVar(t.getType());
  Node k = mkSkolem(v, v.eqNode(t), prefix, comment, flags);
  t.setAttribute(psa, k);
  return k;
}

Node ProofSkolemCache::getWitnessForm(Node n)
{
  return convertInternal(n, true);
}

Node ProofSkolemCache::getSkolemForm(Node n)
{
  return convertInternal(n, false);
}

Node ProofSkolemCache::convertInternal(Node n, bool toWitness)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("pf-skolem-debug") << "ProofSkolemCache::convertInternal: " << toWitness
                           << " " << n << std::endl;
  WitnessFormAttribute wfa;
  SkolemFormAttribute sfa;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      if (toWitness && cur.hasAttribute(wfa))
      {
        visited[cur] = cur.getAttribute(wfa);
      }
      else if (!toWitness && cur.hasAttribute(sfa))
      {
        visited[cur] = cur.getAttribute(sfa);
      }
      else
      {
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const Node& cn : cur)
        {
          visit.push_back(cn);
        }
      }
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      if (toWitness)
      {
        cur.setAttribute(wfa, ret);
      }
      else
      {
        cur.setAttribute(sfa, ret);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Trace("pf-skolem-debug") << "..return " << visited[n] << std::endl;
  return visited[n];
}

void ProofSkolemCache::convertToWitnessFormVec(std::vector<Node>& vec)
{
  for (unsigned i = 0, nvec = vec.size(); i < nvec; i++)
  {
    vec[i] = getWitnessForm(vec[i]);
  }
}
void ProofSkolemCache::convertToSkolemFormVec(std::vector<Node>& vec)
{
  for (unsigned i = 0, nvec = vec.size(); i < nvec; i++)
  {
    vec[i] = getSkolemForm(vec[i]);
  }
}

Node ProofSkolemCache::getOrMakeSkolem(Node w,
                                       const std::string& prefix,
                                       const std::string& comment,
                                       int flags)
{
  Assert(w.getKind() == WITNESS);
  SkolemFormAttribute sfa;
  // could already have a skolem if we used w already
  if (w.hasAttribute(sfa))
  {
    return w.getAttribute(sfa);
  }
  NodeManager* nm = NodeManager::currentNM();
  // make the new skolem
  Node k = nm->mkSkolem(prefix, w.getType(), comment, flags);
  // set witness form attribute for k
  WitnessFormAttribute wfa;
  k.setAttribute(wfa, w);
  // set skolem form attribute for w
  w.setAttribute(sfa, k);
  Trace("pf-skolem") << "ProofSkolemCache::mkSkolem: " << k << " : " << w
                     << std::endl;
  return k;
}

}  // namespace CVC4

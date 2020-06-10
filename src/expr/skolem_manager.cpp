/*********************                                                        */
/*! \file skolem_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of skolem manager class
 **/

#include "expr/skolem_manager.h"

#include "expr/attribute.h"

using namespace CVC4::kind;

namespace CVC4 {

// Attributes are global maps from Nodes to data. Thus, note that these could
// be implemented as internal maps in SkolemManager.
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

Node SkolemManager::mkSkolem(Node v,
                             Node pred,
                             const std::string& prefix,
                             const std::string& comment,
                             int flags,
                             ProofGenerator* pg)
{
  Assert(v.getKind() == BOUND_VARIABLE);
  // make the witness term
  NodeManager* nm = NodeManager::currentNM();
  Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
  // translate pred to witness form, since pred itself may contain skolem
  Node predw = getWitnessForm(pred);
  // make the witness term, which should not contain any skolem
  Node w = nm->mkNode(WITNESS, bvl, predw);
  // store the mapping to proof generator if it exists
  if (pg != nullptr)
  {
    Node q = nm->mkNode(EXISTS, w[0], w[1]);
    // Notice this may overwrite an existing proof generator. This does not
    // matter since either should be able to prove q.
    d_gens[q] = pg;
  }
  return getOrMakeSkolem(w, prefix, comment, flags);
}

Node SkolemManager::mkSkolemize(Node q,
                                std::vector<Node>& skolems,
                                const std::string& prefix,
                                const std::string& comment,
                                int flags,
                                ProofGenerator* pg)
{
  Trace("sk-manager-debug") << "mkSkolemize..." << std::endl;
  Assert(q.getKind() == EXISTS);
  Node currQ = q;
  for (const Node& av : q[0])
  {
    Assert(currQ.getKind() == EXISTS && av == currQ[0][0]);
    // currQ is updated to the result of skolemizing its first variable in
    // the method below.
    Node sk = skolemize(currQ, currQ, prefix, comment, flags);
    Trace("sk-manager-debug")
        << "made skolem " << sk << " for " << av << std::endl;
    skolems.push_back(sk);
  }
  if (pg != nullptr)
  {
    // Same as above, this may overwrite an existing proof generator
    d_gens[q] = pg;
  }
  return currQ;
}

Node SkolemManager::skolemize(Node q,
                              Node& qskolem,
                              const std::string& prefix,
                              const std::string& comment,
                              int flags)
{
  Assert(q.getKind() == EXISTS);
  Node v;
  std::vector<Node> ovars;
  std::vector<Node> ovarsW;
  Trace("sk-manager-debug") << "mkSkolemize..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& av : q[0])
  {
    if (v.isNull())
    {
      v = av;
      continue;
    }
    // must make fresh variable to avoid shadowing, which is unique per
    // variable av to ensure that this method is deterministic. Having this
    // method deterministic ensures that the proof checker (e.g. for
    // quantifiers) is capable of proving the expected value for conclusions
    // of proof rules, instead of an alpha-equivalent variant of a conclusion.
    Node avp = getOrMakeBoundVariable(av, av);
    ovarsW.push_back(avp);
    ovars.push_back(av);
  }
  Assert(!v.isNull());
  Node pred = q[1];
  qskolem = q[1];
  Trace("sk-manager-debug") << "make exists predicate" << std::endl;
  if (!ovars.empty())
  {
    Node bvl = nm->mkNode(BOUND_VAR_LIST, ovarsW);
    pred = nm->mkNode(EXISTS, bvl, pred);
    // skolem form keeps the old variables
    bvl = nm->mkNode(BOUND_VAR_LIST, ovars);
    qskolem = nm->mkNode(EXISTS, bvl, pred);
  }
  Trace("sk-manager-debug") << "call sub mkSkolem" << std::endl;
  // don't use a proof generator, since this may be an intermediate, partially
  // skolemized formula.
  Node k = mkSkolem(v, pred, prefix, comment, flags, nullptr);
  Assert(k.getType() == v.getType());
  TNode tv = v;
  TNode tk = k;
  Trace("sk-manager-debug")
      << "qskolem apply " << tv << " -> " << tk << " to " << pred << std::endl;
  qskolem = qskolem.substitute(tv, tk);
  Trace("sk-manager-debug") << "qskolem done substitution" << std::endl;
  return k;
}

Node SkolemManager::mkPurifySkolem(Node t,
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

Node SkolemManager::mkExistential(Node t, Node p)
{
  Assert(p.getType().isBoolean());
  NodeManager* nm = NodeManager::currentNM();
  Node v = getOrMakeBoundVariable(t, p);
  Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
  Node psubs = p.substitute(TNode(t), TNode(v));
  return nm->mkNode(EXISTS, bvl, psubs);
}

ProofGenerator* SkolemManager::getProofGenerator(Node t)
{
  std::map<Node, ProofGenerator*>::iterator it = d_gens.find(t);
  if (it != d_gens.end())
  {
    return it->second;
  }
  return nullptr;
}

Node SkolemManager::getWitnessForm(Node n) { return convertInternal(n, true); }

Node SkolemManager::getSkolemForm(Node n) { return convertInternal(n, false); }

Node SkolemManager::convertInternal(Node n, bool toWitness)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("sk-manager-debug") << "SkolemManager::convertInternal: " << toWitness
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
        if (cur.getMetaKind() == metakind::PARAMETERIZED)
        {
          visit.push_back(cur.getOperator());
        }
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
        it = visited.find(cur.getOperator());
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cur.getOperator() != it->second;
        children.push_back(it->second);
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
        // notice that WITNESS terms t may be assigned a skolem form that is
        // of kind WITNESS here, if t contains a free variable. This is due to
        // the fact that witness terms in the bodies of quantified formulas are
        // not eliminated and thus may appear in places where getSkolemForm is
        // called on them. Regardless, witness terms with free variables
        // should never be themselves assigned skolems (otherwise we would have
        // assertions with free variables), and thus they can be treated like
        // ordinary terms here.
        cur.setAttribute(sfa, ret);
      }
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Trace("sk-manager-debug") << "..return " << visited[n] << std::endl;
  return visited[n];
}

void SkolemManager::convertToWitnessFormVec(std::vector<Node>& vec)
{
  for (unsigned i = 0, nvec = vec.size(); i < nvec; i++)
  {
    vec[i] = getWitnessForm(vec[i]);
  }
}
void SkolemManager::convertToSkolemFormVec(std::vector<Node>& vec)
{
  for (unsigned i = 0, nvec = vec.size(); i < nvec; i++)
  {
    vec[i] = getSkolemForm(vec[i]);
  }
}

Node SkolemManager::getOrMakeSkolem(Node w,
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
  Trace("sk-manager") << "SkolemManager::mkSkolem: " << k << " : " << w
                      << std::endl;
  return k;
}

Node SkolemManager::getOrMakeBoundVariable(Node t, Node s)
{
  std::pair<Node, Node> key(t, s);
  std::map<std::pair<Node, Node>, Node>::iterator it =
      d_witnessBoundVar.find(key);
  if (it != d_witnessBoundVar.end())
  {
    return it->second;
  }
  TypeNode tt = t.getType();
  Node v = NodeManager::currentNM()->mkBoundVar(tt);
  d_witnessBoundVar[key] = v;
  return v;
}

}  // namespace CVC4

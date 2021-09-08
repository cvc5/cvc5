/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of skolem manager class.
 */

#include "expr/skolem_manager.h"

#include <sstream>

#include "expr/attribute.h"
#include "expr/bound_var_manager.h"
#include "expr/node_algorithm.h"

using namespace cvc5::kind;

namespace cvc5 {

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

struct OriginalFormAttributeId
{
};
typedef expr::Attribute<OriginalFormAttributeId, Node> OriginalFormAttribute;

const char* toString(SkolemFunId id)
{
  switch (id)
  {
    case SkolemFunId::DIV_BY_ZERO: return "DIV_BY_ZERO";
    case SkolemFunId::INT_DIV_BY_ZERO: return "INT_DIV_BY_ZERO";
    case SkolemFunId::MOD_BY_ZERO: return "MOD_BY_ZERO";
    case SkolemFunId::SQRT: return "SQRT";
    case SkolemFunId::SELECTOR_WRONG: return "SELECTOR_WRONG";
    case SkolemFunId::SHARED_SELECTOR: return "SHARED_SELECTOR";
    case SkolemFunId::SEQ_NTH_OOB: return "SEQ_NTH_OOB";
    case SkolemFunId::RE_UNFOLD_POS_COMPONENT: return "RE_UNFOLD_POS_COMPONENT";
    case SkolemFunId::HO_TYPE_MATCH_PRED: return "HO_TYPE_MATCH_PRED";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, SkolemFunId id)
{
  out << toString(id);
  return out;
}

Node SkolemManager::mkSkolem(Node v,
                             Node pred,
                             const std::string& prefix,
                             const std::string& comment,
                             int flags,
                             ProofGenerator* pg)
{
  // We do not currently insist that pred does not contain witness terms
  Assert(v.getKind() == BOUND_VARIABLE);
  // make the witness term
  NodeManager* nm = NodeManager::currentNM();
  Node bvl = nm->mkNode(BOUND_VAR_LIST, v);
  // Make the witness term, where notice that pred may contain skolems. We do
  // not recursively convert pred to witness form, since witness terms should
  // be treated as opaque. Moreover, the use of witness forms leads to
  // variable shadowing issues in e.g. skolemization.
  Node w = nm->mkNode(WITNESS, bvl, pred);
  // store the mapping to proof generator if it exists
  if (pg != nullptr)
  {
    // We cache based on the existential of the original predicate
    Node q = nm->mkNode(EXISTS, bvl, pred);
    // Notice this may overwrite an existing proof generator. This does not
    // matter since either should be able to prove q.
    d_gens[q] = pg;
  }
  Node k = mkSkolemInternal(w, prefix, comment, flags);
  // set witness form attribute for k
  WitnessFormAttribute wfa;
  k.setAttribute(wfa, w);
  Trace("sk-manager-skolem")
      << "skolem: " << k << " witness " << w << std::endl;
  return k;
}

Node SkolemManager::mkSkolemize(Node q,
                                std::vector<Node>& skolems,
                                const std::string& prefix,
                                const std::string& comment,
                                int flags,
                                ProofGenerator* pg)
{
  Trace("sk-manager-debug") << "mkSkolemize " << q << std::endl;
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
  Trace("sk-manager-debug") << "...mkSkolemize returns " << currQ << std::endl;
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
  Trace("sk-manager-debug") << "mkSkolemize..." << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& av : q[0])
  {
    if (v.isNull())
    {
      v = av;
      continue;
    }
    ovars.push_back(av);
  }
  Assert(!v.isNull());
  // make the predicate with one variable stripped off
  Node pred = q[1];
  Trace("sk-manager-debug") << "make exists predicate" << std::endl;
  if (!ovars.empty())
  {
    // keeps the same variables
    Node bvl = nm->mkNode(BOUND_VAR_LIST, ovars);
    // update the predicate
    pred = nm->mkNode(EXISTS, bvl, pred);
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
  // the quantified formula with one step of skolemization
  qskolem = pred.substitute(tv, tk);
  Trace("sk-manager-debug") << "qskolem done substitution" << std::endl;
  return k;
}

Node SkolemManager::mkPurifySkolem(Node t,
                                   const std::string& prefix,
                                   const std::string& comment,
                                   int flags)
{
  Node to = getOriginalForm(t);
  // We do not currently insist that to does not contain witness terms

  Node k = mkSkolemInternal(to, prefix, comment, flags);
  // set original form attribute for k
  OriginalFormAttribute ofa;
  k.setAttribute(ofa, to);

  Trace("sk-manager-skolem")
      << "skolem: " << k << " purify " << to << std::endl;
  return k;
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id,
                                     TypeNode tn,
                                     Node cacheVal,
                                     int flags)
{
  std::tuple<SkolemFunId, TypeNode, Node> key(id, tn, cacheVal);
  std::map<std::tuple<SkolemFunId, TypeNode, Node>, Node>::iterator it =
      d_skolemFuns.find(key);
  if (it == d_skolemFuns.end())
  {
    NodeManager* nm = NodeManager::currentNM();
    std::stringstream ss;
    ss << "SKOLEM_FUN_" << id;
    Node k = nm->mkSkolem(ss.str(), tn, "an internal skolem function", flags);
    d_skolemFuns[key] = k;
    d_skolemFunMap[k] = key;
    return k;
  }
  return it->second;
}

Node SkolemManager::mkSkolemFunction(SkolemFunId id,
                                     TypeNode tn,
                                     const std::vector<Node>& cacheVals,
                                     int flags)
{
  Assert(cacheVals.size() > 1);
  Node cacheVal = NodeManager::currentNM()->mkNode(SEXPR, cacheVals);
  return mkSkolemFunction(id, tn, cacheVal, flags);
}

bool SkolemManager::isSkolemFunction(Node k,
                                     SkolemFunId& id,
                                     Node& cacheVal) const
{
  std::map<Node, std::tuple<SkolemFunId, TypeNode, Node>>::const_iterator it =
      d_skolemFunMap.find(k);
  if (it == d_skolemFunMap.end())
  {
    return false;
  }
  id = std::get<0>(it->second);
  cacheVal = std::get<2>(it->second);
  return true;
}

Node SkolemManager::mkDummySkolem(const std::string& prefix,
                                  const TypeNode& type,
                                  const std::string& comment,
                                  int flags)
{
  return NodeManager::currentNM()->mkSkolem(prefix, type, comment, flags);
}

ProofGenerator* SkolemManager::getProofGenerator(Node t) const
{
  std::map<Node, ProofGenerator*>::const_iterator it = d_gens.find(t);
  if (it != d_gens.end())
  {
    return it->second;
  }
  return nullptr;
}

Node SkolemManager::getWitnessForm(Node k)
{
  Assert(k.getKind() == SKOLEM);
  // simply look up the witness form for k via an attribute
  WitnessFormAttribute wfa;
  return k.getAttribute(wfa);
}

Node SkolemManager::getOriginalForm(Node n)
{
  if (n.isNull())
  {
    return n;
  }
  Trace("sk-manager-debug")
      << "SkolemManager::getOriginalForm " << n << std::endl;
  OriginalFormAttribute ofa;
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node> visited;
  std::unordered_map<TNode, Node>::iterator it;
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
      if (cur.hasAttribute(ofa))
      {
        visited[cur] = cur.getAttribute(ofa);
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
      cur.setAttribute(ofa, ret);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  Trace("sk-manager-debug") << "..return " << visited[n] << std::endl;
  return visited[n];
}

Node SkolemManager::mkSkolemInternal(Node w,
                                     const std::string& prefix,
                                     const std::string& comment,
                                     int flags)
{
  // note that witness, original forms are independent, but share skolems
  NodeManager* nm = NodeManager::currentNM();
  // w is not necessarily a witness term
  SkolemFormAttribute sfa;
  Node k;
  // could already have a skolem if we used w already
  if (w.hasAttribute(sfa))
  {
    return w.getAttribute(sfa);
  }
  // make the new skolem
  if (flags & NodeManager::SKOLEM_BOOL_TERM_VAR)
  {
    Assert (w.getType().isBoolean());
    k = nm->mkBooleanTermVariable();
  }
  else
  {
    k = nm->mkSkolem(prefix, w.getType(), comment, flags);
  }
  // set skolem form attribute for w
  w.setAttribute(sfa, k);
  Trace("sk-manager") << "SkolemManager::mkSkolem: " << k << " : " << w
                      << std::endl;
  return k;
}

}  // namespace cvc5

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof node to s-expression.
 */

#include "proof/proof_node_to_sexpr.h"

#include <iostream>
#include <sstream>

#include "options/proof_options.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "theory/builtin/proof_checker.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

ProofNodeToSExpr::ProofNodeToSExpr(NodeManager* nm) : d_nm(nm)
{
  // use raw symbols so that `:args` is not converted to `|:args|`
  d_conclusionMarker = NodeManager::mkRawSymbol(":conclusion", nm->sExprType());
  d_argsMarker = NodeManager::mkRawSymbol(":args", nm->sExprType());
}

Node ProofNodeToSExpr::convertToSExpr(const ProofNode* pn, bool printConclusion)
{
  std::map<const ProofNode*, Node>::iterator it;
  std::vector<const ProofNode*> visit;
  std::vector<const ProofNode*> traversing;
  const ProofNode* cur;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = d_pnMap.find(cur);

    if (it == d_pnMap.end())
    {
      d_pnMap[cur] = Node::null();
      traversing.push_back(cur);
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        if (std::find(traversing.begin(), traversing.end(), cp.get())
            != traversing.end())
        {
          Unhandled() << "ProofNodeToSExpr::convertToSExpr: cyclic proof! (use "
                         "--proof-check=eager)"
                      << std::endl;
          return Node::null();
        }
        visit.push_back(cp.get());
      }
    }
    else if (it->second.isNull())
    {
      Assert(!traversing.empty());
      traversing.pop_back();
      std::vector<Node> children;
      // add proof rule
      ProofRule r = cur->getRule();
      children.push_back(getOrMkProofRuleVariable(r));
      if (printConclusion)
      {
        children.push_back(d_conclusionMarker);
        children.push_back(cur->getResult());
      }
      const std::vector<std::shared_ptr<ProofNode>>& pc = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& cp : pc)
      {
        it = d_pnMap.find(cp.get());
        Assert(it != d_pnMap.end());
        Assert(!it->second.isNull());
        children.push_back(it->second);
      }
      // add arguments
      const std::vector<Node>& args = cur->getArguments();
      if (!args.empty())
      {
        children.push_back(d_argsMarker);
        // needed to ensure builtin operators are not treated as operators
        std::vector<Node> argsPrint;
        for (size_t i = 0, nargs = args.size(); i < nargs; i++)
        {
          ArgFormat f = getArgumentFormat(cur, i);
          Node av = getArgument(args[i], f);
          argsPrint.push_back(av);
        }
        Node argsC = d_nm->mkNode(Kind::SEXPR, argsPrint);
        children.push_back(argsC);
      }
      d_pnMap[cur] = d_nm->mkNode(Kind::SEXPR, children);
    }
  } while (!visit.empty());
  Assert(d_pnMap.find(pn) != d_pnMap.end());
  Assert(!d_pnMap.find(pn)->second.isNull());
  return d_pnMap[pn];
}

Node ProofNodeToSExpr::getOrMkProofRuleVariable(ProofRule r)
{
  std::map<ProofRule, Node>::iterator it = d_pfrMap.find(r);
  if (it != d_pfrMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << r;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_pfrMap[r] = var;
  return var;
}
Node ProofNodeToSExpr::getOrMkKindVariable(TNode n)
{
  Kind k;
  if (!ProofRuleChecker::getKind(n, k))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected kind node, got " << n;
    return n;
  }
  std::map<Kind, Node>::iterator it = d_kindMap.find(k);
  if (it != d_kindMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << k;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_kindMap[k] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkTheoryIdVariable(TNode n)
{
  theory::TheoryId tid;
  if (!theory::builtin::BuiltinProofRuleChecker::getTheoryId(n, tid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected theory id node, got " << n;
    return n;
  }
  std::map<theory::TheoryId, Node>::iterator it = d_tidMap.find(tid);
  if (it != d_tidMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << tid;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_tidMap[tid] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkMethodIdVariable(TNode n)
{
  MethodId mid;
  if (!getMethodId(n, mid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected method id node, got " << n;
    return n;
  }
  std::map<MethodId, Node>::iterator it = d_midMap.find(mid);
  if (it != d_midMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << mid;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_midMap[mid] = var;
  return var;
}
Node ProofNodeToSExpr::getOrMkTrustIdVariable(TNode n)
{
  TrustId tid;
  if (!getTrustId(n, tid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected trust id node, got " << n;
    return n;
  }
  std::map<TrustId, Node>::iterator it = d_tridMap.find(tid);
  if (it != d_tridMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << tid;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_tridMap[tid] = var;
  return var;
}
Node ProofNodeToSExpr::getOrMkInferenceIdVariable(TNode n)
{
  theory::InferenceId iid;
  if (!theory::getInferenceId(n, iid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected inference id node, got " << n;
    return n;
  }
  std::map<theory::InferenceId, Node>::iterator it = d_iidMap.find(iid);
  if (it != d_iidMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << iid;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_iidMap[iid] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkDslRewriteVariable(TNode n)
{
  ProofRewriteRule rid;
  if (!rewriter::getRewriteRule(n, rid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected inference id node, got " << n;
    return n;
  }
  std::map<ProofRewriteRule, Node>::iterator it = d_dslrMap.find(rid);
  if (it != d_dslrMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << rid;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_dslrMap[rid] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkNodeVariable(TNode n)
{
  std::map<TNode, Node>::iterator it = d_nodeMap.find(n);
  if (it != d_nodeMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << n;
  Node var = NodeManager::mkBoundVar(ss.str(), d_nm->sExprType());
  d_nodeMap[n] = var;
  return var;
}

Node ProofNodeToSExpr::getArgument(Node arg, ArgFormat f)
{
  switch (f)
  {
    case ArgFormat::KIND: return getOrMkKindVariable(arg);
    case ArgFormat::THEORY_ID: return getOrMkTheoryIdVariable(arg);
    case ArgFormat::METHOD_ID: return getOrMkMethodIdVariable(arg);
    case ArgFormat::TRUST_ID: return getOrMkTrustIdVariable(arg);
    case ArgFormat::INFERENCE_ID: return getOrMkInferenceIdVariable(arg);
    case ArgFormat::DSL_REWRITE_ID: return getOrMkDslRewriteVariable(arg);
    case ArgFormat::NODE_VAR: return getOrMkNodeVariable(arg);
    default: return arg;
  }
}

ProofNodeToSExpr::ArgFormat ProofNodeToSExpr::getArgumentFormat(
    const ProofNode* pn, size_t i)
{
  ProofRule r = pn->getRule();
  switch (r)
  {
    case ProofRule::SUBS:
    case ProofRule::MACRO_REWRITE:
    case ProofRule::MACRO_SR_EQ_INTRO:
    case ProofRule::MACRO_SR_PRED_INTRO:
    case ProofRule::MACRO_SR_PRED_TRANSFORM:
      if (i > 0)
      {
        return ArgFormat::METHOD_ID;
      }
      break;
    case ProofRule::MACRO_SR_PRED_ELIM: return ArgFormat::METHOD_ID; break;
    case ProofRule::TRUST_THEORY_REWRITE:
      if (i == 1)
      {
        return ArgFormat::THEORY_ID;
      }
      else if (i == 2)
      {
        return ArgFormat::METHOD_ID;
      }
      break;
    case ProofRule::DSL_REWRITE:
    case ProofRule::THEORY_REWRITE:
      if (i == 0)
      {
        return ArgFormat::DSL_REWRITE_ID;
      }
      break;
    case ProofRule::INSTANTIATE:
    {
      if (i == 1)
      {
        return ArgFormat::INFERENCE_ID;
      }
    }
    break;
    case ProofRule::TRUST:
    {
      if (i == 0)
      {
        return ArgFormat::TRUST_ID;
      }
      else if (i == 2)
      {
        TrustId tid;
        getTrustId(pn->getArguments()[0], tid);
        if (tid == TrustId::THEORY_LEMMA)
        {
          return ArgFormat::THEORY_ID;
        }
      }
    }
    break;
    default: break;
  }
  return ArgFormat::DEFAULT;
}

}  // namespace cvc5::internal

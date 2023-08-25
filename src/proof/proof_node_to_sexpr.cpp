/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

ProofNodeToSExpr::ProofNodeToSExpr()
{
  NodeManager* nm = NodeManager::currentNM();
  // use raw symbols so that `:args` is not converted to `|:args|`
  d_conclusionMarker = nm->mkRawSymbol(":conclusion", nm->sExprType());
  d_argsMarker = nm->mkRawSymbol(":args", nm->sExprType());
}

Node ProofNodeToSExpr::convertToSExpr(const ProofNode* pn, bool printConclusion)
{
  NodeManager* nm = NodeManager::currentNM();
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
      PfRule r = cur->getRule();
      children.push_back(getOrMkPfRuleVariable(r));
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
        // this can be the case for CONG where d_args may contain a builtin
        // operator
        std::vector<Node> argsPrint;
        for (size_t i = 0, nargs = args.size(); i < nargs; i++)
        {
          ArgFormat f = getArgumentFormat(cur, i);
          Node av = getArgument(args[i], f);
          argsPrint.push_back(av);
        }
        Node argsC = nm->mkNode(SEXPR, argsPrint);
        children.push_back(argsC);
      }
      d_pnMap[cur] = nm->mkNode(SEXPR, children);
    }
  } while (!visit.empty());
  Assert(d_pnMap.find(pn) != d_pnMap.end());
  Assert(!d_pnMap.find(pn)->second.isNull());
  return d_pnMap[pn];
}

Node ProofNodeToSExpr::getOrMkPfRuleVariable(PfRule r)
{
  std::map<PfRule, Node>::iterator it = d_pfrMap.find(r);
  if (it != d_pfrMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << r;
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
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
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
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
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
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
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
  d_midMap[mid] = var;
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
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
  d_iidMap[iid] = var;
  return var;
}

Node ProofNodeToSExpr::getOrMkDslRewriteVariable(TNode n)
{
  rewriter::DslPfRule rid;
  if (!rewriter::getDslPfRule(n, rid))
  {
    // just use self if we failed to get the node, throw a debug failure
    Assert(false) << "Expected inference id node, got " << n;
    return n;
  }
  std::map<rewriter::DslPfRule, Node>::iterator it = d_dslrMap.find(rid);
  if (it != d_dslrMap.end())
  {
    return it->second;
  }
  std::stringstream ss;
  ss << rid;
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
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
  NodeManager* nm = NodeManager::currentNM();
  Node var = nm->mkBoundVar(ss.str(), nm->sExprType());
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
    case ArgFormat::INFERENCE_ID: return getOrMkInferenceIdVariable(arg);
    case ArgFormat::DSL_REWRITE_ID: return getOrMkDslRewriteVariable(arg);
    case ArgFormat::NODE_VAR: return getOrMkNodeVariable(arg);
    default: return arg;
  }
}

ProofNodeToSExpr::ArgFormat ProofNodeToSExpr::getArgumentFormat(
    const ProofNode* pn, size_t i)
{
  PfRule r = pn->getRule();
  switch (r)
  {
    case PfRule::CONG:
    {
      if (i == 0)
      {
        return ArgFormat::KIND;
      }
      const std::vector<Node>& args = pn->getArguments();
      Assert(i < args.size());
      if (args[i].getNumChildren() == 0
          && NodeManager::operatorToKind(args[i]) != UNDEFINED_KIND)
      {
        return ArgFormat::NODE_VAR;
      }
    }
    break;
    case PfRule::SUBS:
    case PfRule::REWRITE:
    case PfRule::MACRO_SR_EQ_INTRO:
    case PfRule::MACRO_SR_PRED_INTRO:
    case PfRule::MACRO_SR_PRED_TRANSFORM:
      if (i > 0)
      {
        return ArgFormat::METHOD_ID;
      }
      break;
    case PfRule::MACRO_SR_PRED_ELIM: return ArgFormat::METHOD_ID; break;
    case PfRule::THEORY_LEMMA:
    case PfRule::THEORY_REWRITE:
      if (i == 1)
      {
        return ArgFormat::THEORY_ID;
      }
      else if (r == PfRule::THEORY_REWRITE && i == 2)
      {
        return ArgFormat::METHOD_ID;
      }
      break;
    case PfRule::DSL_REWRITE:
      if (i == 0)
      {
        return ArgFormat::DSL_REWRITE_ID;
      }
      break;
    case PfRule::INSTANTIATE:
    {
      Assert(!pn->getChildren().empty());
      Node q = pn->getChildren()[0]->getResult();
      Assert(q.getKind() == kind::FORALL);
      if (i == q[0].getNumChildren())
      {
        return ArgFormat::INFERENCE_ID;
      }
    }
    break;
    case PfRule::ANNOTATION:
      if (i == 0)
      {
        return ArgFormat::INFERENCE_ID;
      }
      break;
    default: break;
  }
  return ArgFormat::DEFAULT;
}

}  // namespace cvc5::internal

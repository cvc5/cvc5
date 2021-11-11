/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/uf_options.h"
#include "smt/env.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace uf {

LambdaLift::LambdaLift(Env& env)
    : EnvObj(env),
      d_lifted(userContext()),
      d_lambdaMap(userContext()),
      d_epg(env.isTheoryProofProducing() ? new EagerProofGenerator(
                env.getProofNodeManager(), userContext(), "LambdaLift::epg")
                                         : nullptr)
{
}

TrustNode LambdaLift::lift(Node node)
{
  if (d_lifted.find(node) != d_lifted.end())
  {
    return TrustNode::null();
  }
  d_lifted.insert(node);
  Node assertion = getAssertionFor(node);
  if (assertion.isNull())
  {
    return TrustNode::null();
  }
  // if no proofs, return lemma with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustLemma(assertion);
  }
  return d_epg->mkTrustNode(
      assertion, PfRule::MACRO_SR_PRED_INTRO, {}, {assertion});
}

TrustNode LambdaLift::ppRewrite(Node node, std::vector<SkolemLemma>& lems)
{
  TNode skolem = getSkolemFor(node);
  if (skolem.isNull())
  {
    return TrustNode::null();
  }
  d_lambdaMap[skolem] = node;
  if (!options().uf.ufHoLazyLambdaLift)
  {
    TrustNode trn = lift(node);
    lems.push_back(SkolemLemma(trn, skolem));
  }
  // if no proofs, return lemma with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustRewrite(node, skolem);
  }
  Node eq = node.eqNode(skolem);
  return d_epg->mkTrustedRewrite(
      node, skolem, PfRule::MACRO_SR_PRED_INTRO, {eq});
}

Node LambdaLift::getLambdaFor(TNode skolem) const
{
  NodeNodeMap::const_iterator it = d_lambdaMap.find(skolem);
  if (it == d_lambdaMap.end())
  {
    return Node::null();
  }
  return it->second;
}

bool LambdaLift::isLambdaFunction(TNode n) const
{
  return !getLambdaFor(n).isNull();
}

Node LambdaLift::getAssertionFor(TNode node)
{
  TNode skolem = getSkolemFor(node);
  if (skolem.isNull())
  {
    return Node::null();
  }
  Kind k = node.getKind();
  Node assertion;
  if (k == LAMBDA)
  {
    NodeManager* nm = NodeManager::currentNM();
    // The new assertion
    std::vector<Node> children;
    // bound variable list
    children.push_back(node[0]);
    // body
    std::vector<Node> skolem_app_c;
    skolem_app_c.push_back(skolem);
    skolem_app_c.insert(skolem_app_c.end(), node[0].begin(), node[0].end());
    Node skolem_app = nm->mkNode(APPLY_UF, skolem_app_c);
    children.push_back(skolem_app.eqNode(node[1]));
    // axiom defining skolem
    assertion = nm->mkNode(FORALL, children);

    // Lambda lifting is trivial to justify, hence we don't set a proof
    // generator here. In particular, replacing the skolem introduced
    // here with its original lambda ensures the new assertion rewrites
    // to true.
    // For example, if (lambda y. t[y]) has skolem k, then this lemma is:
    //   forall x. k(x)=t[x]
    // whose witness form rewrites
    //   forall x. (lambda y. t[y])(x)=t[x] --> forall x. t[x]=t[x] --> true
  }
  return assertion;
}

Node LambdaLift::getSkolemFor(TNode node)
{
  Node skolem;
  Kind k = node.getKind();
  if (k == LAMBDA)
  {
    // if a lambda, return the purification variable for the node. We ignore
    // lambdas with free variables, which can occur beneath quantifiers
    // during preprocessing.
    if (!expr::hasFreeVar(node))
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make LAMBDA skolem" << std::endl;
      // Make the skolem to represent the lambda
      NodeManager* nm = NodeManager::currentNM();
      SkolemManager* sm = nm->getSkolemManager();
      skolem = sm->mkPurifySkolem(
          node,
          "lambdaF",
          "a function introduced due to term-level lambda removal");
    }
  }
  return skolem;
}

TrustNode LambdaLift::betaReduce(TNode node) const
{
  Kind k = node.getKind();
  if (k == APPLY_UF)
  {
    Node op = node.getOperator();
    Node opl = getLambdaFor(op);
    if (!opl.isNull())
    {
      std::vector<Node> args(node.begin(), node.end());
      Node app = betaReduce(opl, args);
      Trace("uf-lazy-ll") << "Beta reduce: " << node << " -> " << app
                          << std::endl;
      if (d_epg == nullptr)
      {
        return TrustNode::mkTrustRewrite(node, app);
      }
      return d_epg->mkTrustedRewrite(
          node, app, PfRule::MACRO_SR_PRED_INTRO, {node.eqNode(app)});
    }
  }
  // otherwise, unchanged
  return TrustNode::null();
}

Node LambdaLift::betaReduce(TNode lam, const std::vector<Node>& args) const
{
  Assert(lam.getKind() == LAMBDA);
  NodeManager* nm = NodeManager::currentNM();
  std::vector<Node> betaRed;
  betaRed.push_back(lam);
  betaRed.insert(betaRed.end(), args.begin(), args.end());
  Node app = nm->mkNode(APPLY_UF, betaRed);
  app = rewrite(app);
  return app;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5

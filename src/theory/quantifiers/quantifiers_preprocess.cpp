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
 * Preprocessor for the theory of quantifiers.
 */

#include "theory/quantifiers/quantifiers_preprocess.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/skolemize.h"
#include "expr/node_algorithm.h"
#include "theory/quantifiers/quantifiers_rewriter.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersPreprocess::QuantifiersPreprocess(Env& env) : EnvObj(env){}
   
Node QuantifiersPreprocess::computePrenexAgg(Node n,
                                           std::map<Node, Node>& visited) const
{
  std::map<Node, Node>::iterator itv = visited.find(n);
  if (itv != visited.end())
  {
    return itv->second;
  }
  if (!expr::hasClosure(n))
  {
    // trivial
    return n;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node ret = n;
  if (n.getKind() == NOT)
  {
    ret = computePrenexAgg(n[0], visited).negate();
  }
  else if (n.getKind() == FORALL)
  {
    std::vector<Node> children;
    children.push_back(computePrenexAgg(n[1], visited));
    std::vector<Node> args;
    args.insert(args.end(), n[0].begin(), n[0].end());
    // for each child, strip top level quant
    for (unsigned i = 0; i < children.size(); i++)
    {
      if (children[i].getKind() == FORALL)
      {
        args.insert(args.end(), children[i][0].begin(), children[i][0].end());
        children[i] = children[i][1];
      }
    }
    // keep the pattern
    std::vector<Node> iplc;
    if (n.getNumChildren() == 3)
    {
      iplc.insert(iplc.end(), n[2].begin(), n[2].end());
    }
    Node nb = nm->mkOr(children);
    ret = QuantifiersRewriter::mkForall(args, nb, iplc, true);
  }
  else
  {
    std::unordered_set<Node> argsSet;
    std::unordered_set<Node> nargsSet;
    Node q;
    Node nn = QuantifiersRewriter::computePrenex(q, n, argsSet, nargsSet, true, true);
    Assert(n != nn || argsSet.empty());
    Assert(n != nn || nargsSet.empty());
    if (n != nn)
    {
      Node nnn = computePrenexAgg(nn, visited);
      // merge prenex
      if (nnn.getKind() == FORALL)
      {
        argsSet.insert(nnn[0].begin(), nnn[0].end());
        nnn = nnn[1];
        // pos polarity variables are inner
        if (!argsSet.empty())
        {
          nnn = QuantifiersRewriter::mkForall({argsSet.begin(), argsSet.end()}, nnn, true);
        }
        argsSet.clear();
      }
      else if (nnn.getKind() == NOT && nnn[0].getKind() == FORALL)
      {
        nargsSet.insert(nnn[0][0].begin(), nnn[0][0].end());
        nnn = nnn[0][1].negate();
      }
      if (!nargsSet.empty())
      {
        nnn = QuantifiersRewriter::mkForall({nargsSet.begin(), nargsSet.end()}, nnn.negate(), true)
                  .negate();
      }
      if (!argsSet.empty())
      {
        nnn = QuantifiersRewriter::mkForall({argsSet.begin(), argsSet.end()}, nnn, true);
      }
      ret = nnn;
    }
  }
  visited[n] = ret;
  return ret;
}

Node QuantifiersPreprocess::preSkolemizeQuantifiers(
    Node n,
    bool polarity,
    std::vector<TypeNode>& fvTypes,
    std::vector<TNode>& fvs) const
{
  NodeManager * nm = NodeManager::currentNM();
  Trace("pre-sk") << "Pre-skolem " << n << " " << polarity << " " << fvs.size()
                  << std::endl;
  if (n.getKind() == NOT)
  {
    Node nn = preSkolemizeQuantifiers(n[0], !polarity, fvTypes, fvs);
    return nn.negate();
  }
  else if (n.getKind() == FORALL)
  {
    if (n.getNumChildren() == 3)
    {
      // Do not pre-skolemize quantified formulas with three children.
      // This includes non-standard quantified formulas
      // like recursive function definitions, or sygus conjectures, and
      // quantified formulas with triggers.
      return n;
    }
    else if (polarity)
    {
      if (options().quantifiers.preSkolemQuant && options().quantifiers.preSkolemQuantNested)
      {
        std::vector<Node> children;
        children.push_back(n[0]);
        // add children to current scope
        std::vector<TypeNode> fvt;
        std::vector<TNode> fvss;
        fvt.insert(fvt.begin(), fvTypes.begin(), fvTypes.end());
        fvss.insert(fvss.begin(), fvs.begin(), fvs.end());
        for (int i = 0; i < (int)n[0].getNumChildren(); i++)
        {
          fvt.push_back(n[0][i].getType());
          fvss.push_back(n[0][i]);
        }
        // process body
        children.push_back(preSkolemizeQuantifiers(n[1], polarity, fvt, fvss));
        // return processed quantifier
        return nm->mkNode(FORALL, children);
      }
    }
    else
    {
      // process body
      Node nn = preSkolemizeQuantifiers(n[1], polarity, fvTypes, fvs);
      std::vector<Node> sk;
      Node sub;
      std::vector<unsigned> sub_vars;
      // return skolemized body
      return Skolemize::mkSkolemizedBody(
          n, nn, fvTypes, fvs, sk, sub, sub_vars);
    }
  }
  else
  {
    // check if it contains a quantifier as a subterm
    // if so, we will write this node
    if (expr::hasClosure(n))
    {
      if ((n.getKind() == ITE && n.getType().isBoolean())
          || (n.getKind() == EQUAL && n[0].getType().isBoolean()))
      {
        if (options().quantifiers.preSkolemQuantAgg)
        {
          Node nn;
          // must remove structure
          if (n.getKind() == ITE)
          {
            nn = nm->mkNode(
                AND,
                nm->mkNode(
                    OR, n[0].notNode(), n[1]),
                nm->mkNode(OR, n[0], n[2]));
          }
          else if (n.getKind() == EQUAL)
          {
            nn = nm->mkNode(
                AND,
                nm->mkNode(
                    OR,
                    n[0].notNode(),
                    n.getKind() == XOR ? n[1].notNode() : n[1]),
                nm->mkNode(
                    OR,
                    n[0],
                    n.getKind() == XOR ? n[1] : n[1].notNode()));
          }
          return preSkolemizeQuantifiers(nn, polarity, fvTypes, fvs);
        }
      }
      else if (n.getKind() == AND || n.getKind() == OR)
      {
        std::vector<Node> children;
        for (int i = 0; i < (int)n.getNumChildren(); i++)
        {
          children.push_back(
              preSkolemizeQuantifiers(n[i], polarity, fvTypes, fvs));
        }
        return nm->mkNode(n.getKind(), children);
      }
    }
  }
  return n;
}

TrustNode QuantifiersPreprocess::preprocess(Node n, bool isInst) const
{
  Node prev = n;
  if (options().quantifiers.preSkolemQuant)
  {
    if (!isInst || !options().quantifiers.preSkolemQuantNested)
    {
      Trace("quantifiers-preprocess-debug")
          << "Pre-skolemize " << n << "..." << std::endl;
      // apply pre-skolemization to existential quantifiers
      std::vector<TypeNode> fvTypes;
      std::vector<TNode> fvs;
      n = preSkolemizeQuantifiers(prev, true, fvTypes, fvs);
    }
  }
  // pull all quantifiers globally
  if (options().quantifiers.prenexQuant == options::PrenexQuantMode::NORMAL)
  {
    Trace("quantifiers-prenex") << "Prenexing : " << n << std::endl;
    std::map<Node, Node> visited;
    n = computePrenexAgg(n, visited);
    n = rewrite(n);
    Trace("quantifiers-prenex") << "Prenexing returned : " << n << std::endl;
  }
  if (n != prev)
  {
    Trace("quantifiers-preprocess") << "Preprocess " << prev << std::endl;
    Trace("quantifiers-preprocess") << "..returned " << n << std::endl;
    return TrustNode::mkTrustRewrite(prev, n, nullptr);
  }
  return TrustNode::null();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

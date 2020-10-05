/*********************                                                        */
/*! \file model_blocker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utility for blocking models.
 **
 **/

#include "smt/model_blocker.h"

#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;

namespace CVC4 {

Expr ModelBlocker::getModelBlocker(const std::vector<Expr>& assertions,
                                   theory::TheoryModel* m,
                                   options::BlockModelsMode mode,
                                   const std::vector<Expr>& exprToBlock)
{
  NodeManager* nm = NodeManager::currentNM();
  // convert to nodes
  std::vector<Node> tlAsserts;
  for (const Expr& a : assertions)
  {
    Node an = Node::fromExpr(a);
    tlAsserts.push_back(an);
  }
  std::vector<Node> nodesToBlock;
  for (const Expr& eb : exprToBlock)
  {
    nodesToBlock.push_back(Node::fromExpr(eb));
  }
  Trace("model-blocker") << "Compute model blocker, assertions:" << std::endl;
  Node blocker;
  if (mode == options::BlockModelsMode::LITERALS)
  {
    Assert(nodesToBlock.empty());
    // optimization: filter out top-level unit assertions, as they cannot
    // contribute to model blocking.
    unsigned counter = 0;
    std::vector<Node> asserts;
    while (counter < tlAsserts.size())
    {
      Node cur = tlAsserts[counter];
      counter++;
      Node catom = cur.getKind() == NOT ? cur[0] : cur;
      bool cpol = cur.getKind() != NOT;
      if (catom.getKind() == NOT)
      {
        tlAsserts.push_back(catom[0]);
      }
      else if (catom.getKind() == AND && cpol)
      {
        tlAsserts.insert(tlAsserts.end(), catom.begin(), catom.end());
      }
      else if (theory::quantifiers::TermUtil::isBoolConnectiveTerm(catom))
      {
        asserts.push_back(cur);
        Trace("model-blocker") << "  " << cur << std::endl;
      }
    }
    if (asserts.empty())
    {
      Node blockTriv = nm->mkConst(false);
      Trace("model-blocker")
          << "...model blocker is (trivially) " << blockTriv << std::endl;
      return blockTriv.toExpr();
    }

    Node formula = asserts.size() > 1 ? nm->mkNode(AND, asserts) : asserts[0];
    std::unordered_map<TNode, Node, TNodeHashFunction> visited;
    std::unordered_map<TNode, Node, TNodeHashFunction> implicant;
    std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
    std::vector<TNode> visit;
    TNode cur;
    visit.push_back(formula);
    do
    {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);

      Trace("model-blocker-debug") << "Visit : " << cur << std::endl;

      if (it == visited.end())
      {
        visited[cur] = Node::null();
        Node catom = cur.getKind() == NOT ? cur[0] : cur;
        bool cpol = cur.getKind() != NOT;
        // compute the implicant
        // impl is a formula that implies cur that is also satisfied by m
        Node impl;
        if (catom.getKind() == NOT)
        {
          // double negation
          impl = catom[0];
        }
        else if (catom.getKind() == OR || catom.getKind() == AND)
        {
          // if disjunctive
          if ((catom.getKind() == OR) == cpol)
          {
            // take the first literal that is satisfied
            for (Node n : catom)
            {
              // rewrite, this ensures that e.g. the propositional value of
              // quantified formulas can be queried
              n = theory::Rewriter::rewrite(n);
              Node vn = Node::fromExpr(m->getValue(n.toExpr()));
              Assert(vn.isConst());
              if (vn.getConst<bool>() == cpol)
              {
                impl = cpol ? n : n.negate();
                break;
              }
            }
          }
          else if (catom.getKind() == OR)
          {
            // one step NNF
            std::vector<Node> children;
            for (const Node& cn : catom)
            {
              children.push_back(cn.negate());
            }
            impl = nm->mkNode(AND, children);
          }
        }
        else if (catom.getKind() == ITE)
        {
          Node vcond = Node::fromExpr(m->getValue(cur[0].toExpr()));
          Assert(vcond.isConst());
          Node cond = cur[0];
          Node branch;
          if (vcond.getConst<bool>())
          {
            branch = cur[1];
          }
          else
          {
            cond = cond.negate();
            branch = cur[2];
          }
          impl = nm->mkNode(AND, cond, cpol ? branch : branch.negate());
        }
        else if ((catom.getKind() == EQUAL && catom[0].getType().isBoolean())
                 || catom.getKind() == XOR)
        {
          // based on how the children evaluate in the model
          std::vector<Node> children;
          for (const Node& cn : catom)
          {
            Node vn = Node::fromExpr(m->getValue(cn.toExpr()));
            Assert(vn.isConst());
            children.push_back(vn.getConst<bool>() ? cn : cn.negate());
          }
          impl = nm->mkNode(AND, children);
        }
        else
        {
          // literals justified by themselves
          visited[cur] = cur;
          Trace("model-blocker-debug") << "...self justified" << std::endl;
        }
        if (visited[cur].isNull())
        {
          visit.push_back(cur);
          if (impl.isNull())
          {
            Assert(cur.getKind() == AND);
            Trace("model-blocker-debug") << "...recurse" << std::endl;
            visit.insert(visit.end(), cur.begin(), cur.end());
          }
          else
          {
            Trace("model-blocker-debug")
                << "...implicant : " << impl << std::endl;
            implicant[cur] = impl;
            visit.push_back(impl);
          }
        }
      }
      else if (it->second.isNull())
      {
        Node ret = cur;
        it = implicant.find(cur);
        if (it != implicant.end())
        {
          Node impl = it->second;
          it = visited.find(impl);
          Assert(it != visited.end());
          Assert(!it->second.isNull());
          ret = it->second;
          Trace("model-blocker-debug")
              << "...implicant res: " << ret << std::endl;
        }
        else
        {
          bool childChanged = false;
          std::vector<Node> children;
          // we never recurse to parameterized nodes
          Assert(cur.getMetaKind() != metakind::PARAMETERIZED);
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
          Trace("model-blocker-debug") << "...recons res: " << ret << std::endl;
        }
        visited[cur] = ret;
      }
    } while (!visit.empty());
    Assert(visited.find(formula) != visited.end());
    Assert(!visited.find(formula)->second.isNull());
    blocker = visited[formula].negate();
  }
  else
  {
    Assert(mode == options::BlockModelsMode::VALUES);
    std::vector<Node> blockers;
    // if specific terms were not specified, block all variables of
    // the model
    if (nodesToBlock.empty())
    {
      Trace("model-blocker")
          << "no specific terms to block recognized" << std::endl;
      std::unordered_set<Node, NodeHashFunction> symbols;
      for (Node n : tlAsserts)
      {
        expr::getSymbols(n, symbols);
      }
      for (Node s : symbols)
      {
        if (s.getType().getKind() != kind::FUNCTION_TYPE)
        {
          Node v = m->getValue(s);
          Node a = nm->mkNode(DISTINCT, s, v);
          blockers.push_back(a);
        }
      }
    }
    // otherwise, block all terms that were specified in get-value
    else
    {
      std::unordered_set<Node, NodeHashFunction> terms;
      for (Node n : nodesToBlock)
      {
        Node v = m->getValue(n);
        Node a = nm->mkNode(DISTINCT, n, v);
        blockers.push_back(a);
      }
    }
    if (blockers.size() == 0)
    {
      blocker = nm->mkConst<bool>(true);
    }
    else if (blockers.size() == 1)
    {
      blocker = blockers[0];
    }
    else
    {
      blocker = nm->mkNode(OR, blockers);
    }
  }
  Trace("model-blocker") << "...model blocker is " << blocker << std::endl;
  return blocker.toExpr();
}

} /* namespace CVC4 */

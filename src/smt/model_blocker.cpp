/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utility for blocking models.
 */

#include "smt/model_blocker.h"

#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

ModelBlocker::ModelBlocker(Env& e) : EnvObj(e) {}

Node ModelBlocker::getModelBlocker(const std::vector<Node>& assertions,
                                   theory::TheoryModel* m,
                                   modes::BlockModelsMode mode,
                                   const std::vector<Node>& exprToBlock)
{
  NodeManager* nm = NodeManager::currentNM();
  // convert to nodes
  std::vector<Node> tlAsserts = assertions;
  std::vector<Node> nodesToBlock = exprToBlock;
  Trace("model-blocker") << "Compute model blocker, assertions:" << std::endl;
  Node blocker;
  if (mode == modes::BlockModelsMode::LITERALS)
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
      return blockTriv;
    }

    Node formula = asserts.size() > 1 ? nm->mkNode(AND, asserts) : asserts[0];
    std::unordered_map<TNode, Node> visited;
    std::unordered_map<TNode, Node> implicant;
    std::unordered_map<TNode, Node>::iterator it;
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
              n = rewrite(n);
              Node vn = m->getValue(n);
              if (vn.isConst() && vn.getConst<bool>() == cpol)
              {
                impl = cpol ? n : n.negate();
                break;
              }
            }
            if (impl.isNull())
            {
              // unknown value, take self
              visited[cur] = cur;
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
          Node vcond = m->getValue(catom[0]);
          if (vcond.isConst())
          {
            Node cond = catom[0];
            Node branch;
            if (vcond.getConst<bool>())
            {
              branch = catom[1];
            }
            else
            {
              cond = cond.negate();
              branch = catom[2];
            }
            impl = nm->mkNode(AND, cond, cpol ? branch : branch.negate());
          }
          else
          {
            // unknown value, take self
            visited[cur] = cur;
          }
        }
        else if ((catom.getKind() == EQUAL && catom[0].getType().isBoolean())
                 || catom.getKind() == XOR)
        {
          // based on how the children evaluate in the model
          std::vector<Node> children;
          bool success = true;
          for (const Node& cn : catom)
          {
            Node vn = m->getValue(cn);
            if (!vn.isConst())
            {
              success = false;
              break;
            }
            children.push_back(vn.getConst<bool>() ? cn : cn.negate());
          }
          if (success)
          {
            impl = nm->mkNode(AND, children);
          }
          else
          {
            // unknown value, take self
            visited[cur] = cur;
          }
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
    Assert(mode == modes::BlockModelsMode::VALUES);
    std::vector<Node> blockers;
    // if specific terms were not specified, block all variables of
    // the model
    if (nodesToBlock.empty())
    {
      Trace("model-blocker")
          << "no specific terms to block recognized" << std::endl;
      std::unordered_set<Node> symbols;
      for (Node n : tlAsserts)
      {
        expr::getSymbols(n, symbols);
      }
      for (Node s : symbols)
      {
        if (!s.getType().isFirstClass())
        {
          // ignore e.g. constructors
          continue;
        }
        if (!logicInfo().isHigherOrder()
            && s.getType().getKind() == kind::FUNCTION_TYPE)
        {
          // ignore functions if not higher-order
          continue;
        }
        nodesToBlock.push_back(s);
      }
    }
    // otherwise, block all terms that were specified in get-value
    std::map<TypeNode, std::vector<Node> > nonClosedEnum;
    std::map<Node, Node> nonClosedValue;
    std::unordered_set<Node> terms;
    for (const Node& n : nodesToBlock)
    {
      TypeNode tn = n.getType();
      Node v = m->getValue(n);
      if (tn.isClosedEnumerable())
      {
        // if its type is closed enumerable, then we can block its value
        Node a = n.eqNode(v).notNode();
        blockers.push_back(a);
      }
      else
      {
        nonClosedValue[n] = v;
        // otherwise we will block (dis)equality with other variables of its
        // type below
        nonClosedEnum[tn].push_back(n);
      }
    }
    for (const std::pair<const TypeNode, std::vector<Node> >& es :
         nonClosedEnum)
    {
      size_t nenum = es.second.size();
      for (size_t i = 0; i < nenum; i++)
      {
        const Node& vi = nonClosedValue[es.second[i]];
        for (size_t j = (i + 1); j < nenum; j++)
        {
          const Node& vj = nonClosedValue[es.second[j]];
          Node eq = es.second[i].eqNode(es.second[j]);
          if (vi == vj)
          {
            eq = eq.notNode();
          }
          blockers.push_back(eq);
        }
      }
    }
    blocker = nm->mkOr(blockers);
  }
  Trace("model-blocker") << "...model blocker is " << blocker << std::endl;
  return blocker;
}

}  // namespace cvc5::internal

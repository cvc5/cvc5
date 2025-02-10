/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utility for blocking models.
 */

#include "smt/model_blocker.h"

#include "base/modal_exception.h"
#include "expr/node.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "theory/logic_info.h"
#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"
#include "expr/subs.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

ModelBlocker::ModelBlocker(Env& e) : EnvObj(e) {}

Node ModelBlocker::getModelBlocker(const std::vector<Node>& assertions,
                                   theory::TheoryModel* m,
                                   modes::BlockModelsMode mode,
                                   const std::vector<Node>& exprToBlock)
{
  NodeManager* nm = nodeManager();
  // convert to nodes
  std::vector<Node> tlAsserts = assertions;
  std::vector<Node> nodesToBlock = exprToBlock;
  Trace("model-blocker") << "Compute model blocker, assertions:" << std::endl;
  // the list of literals that should be blocked
  std::unordered_set<Node> blockers;
  // a subset of the above vector that holds on top level
  std::unordered_set<Node> blockersTriv;
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
      Node catom = cur.getKind() == Kind::NOT ? cur[0] : cur;
      bool cpol = cur.getKind() != Kind::NOT;
      if (catom.getKind() == Kind::NOT)
      {
        tlAsserts.push_back(catom[0]);
      }
      else if (catom.getKind() == Kind::AND && cpol)
      {
        tlAsserts.insert(tlAsserts.end(), catom.begin(), catom.end());
      }
      else if (theory::quantifiers::TermUtil::isBoolConnectiveTerm(catom))
      {
        asserts.push_back(cur);
        Trace("model-blocker") << "  " << cur << std::endl;
      }
      else
      {
        // otherwise store that the blocker is trivial
        blockersTriv.insert(cur);
        blockers.insert(cur);
      }
    }
    std::unordered_set<TNode> visited;
    std::unordered_set<TNode>::iterator it;
    std::vector<TNode> visit;
    visit.insert(visit.end(), asserts.begin(), asserts.end());
    TNode cur;
    do
    {
      cur = visit.back();
      visit.pop_back();
      it = visited.find(cur);

      Trace("model-blocker-debug") << "Visit : " << cur << std::endl;

      if (it == visited.end())
      {
        visited.insert(cur);
        Node catom = cur.getKind() == Kind::NOT ? cur[0] : cur;
        bool cpol = cur.getKind() != Kind::NOT;
        // compute the implicant
        // impl is a formula that implies cur that is also satisfied by m
        Node impl;
        if (catom.getKind() == Kind::NOT)
        {
          // double negation
          impl = catom[0];
        }
        else if (catom.getKind() == Kind::OR || catom.getKind() == Kind::AND)
        {
          // if disjunctive
          if ((catom.getKind() == Kind::OR) == cpol)
          {
            // take the first literal that is satisfied
            for (const Node& n : catom)
            {
              // rewrite, this ensures that e.g. the propositional value of
              // quantified formulas can be queried
              Node nr = rewrite(n);
              Node vn = m->getValue(nr);
              if (vn.isConst() && vn.getConst<bool>() == cpol)
              {
                impl = cpol ? nr : nr.negate();
                break;
              }
            }
            if (impl.isNull())
            {
              // unknown value, take self
              blockers.insert(cur);
            }
          }
          else if (catom.getKind() == Kind::OR)
          {
            // one step NNF
            std::vector<Node> children;
            for (const Node& cn : catom)
            {
              children.push_back(cn.negate());
            }
            impl = nm->mkNode(Kind::AND, children);
          }
          else
          {
            // otherwise a positive AND, recurse on this below
            impl = cur;
          }
        }
        else if (catom.getKind() == Kind::ITE)
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
            impl = nm->mkNode(Kind::AND, cond, cpol ? branch : branch.negate());
          }
          else
          {
            // unknown value, take self
            blockers.insert(cur);
          }
        }
        else if ((catom.getKind() == Kind::EQUAL
                  && catom[0].getType().isBoolean())
                || catom.getKind() == Kind::XOR)
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
            impl = nm->mkNode(Kind::AND, children);
          }
          else
          {
            // unknown value, take self
            blockers.insert(cur);
          }
        }
        else
        {
          // literals justified by themselves
          blockers.insert(cur);
          Trace("model-blocker-debug") << "...self justified" << std::endl;
        }
        if (!impl.isNull())
        {
          if  (impl.getKind() == Kind::AND)
          {
            Trace("model-blocker-debug") << "...recurse" << std::endl;
            visit.insert(visit.end(), impl.begin(), impl.end());
          }
          else
          {
            visit.emplace_back(impl);
          }
        }
      }
    } while (!visit.empty());
  }
  else
  {
    Assert(mode == modes::BlockModelsMode::VALUES);
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
            && s.getType().getKind() == Kind::FUNCTION_TYPE)
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
        Node a = n.eqNode(v);
        blockers.insert(a);
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
          if (vi != vj)
          {
            eq = eq.notNode();
          }
          blockers.insert(eq);
        }
      }
    }
  }
  // minimize, if in literals mode
  bool minBlocker = (mode == modes::BlockModelsMode::LITERALS);
  if (minBlocker)
  {
    Subs s;
    std::vector<Node> possible;
    std::vector<Node> bvec(blockers.begin(), blockers.end());
    blockers.clear();
    for (const Node& a : bvec)
    {
      if (a.getKind() == Kind::EQUAL)
      {
        // if it is an equality between a variable, turn into a substitution,
        // which will help prune below.
        Node as = s.apply(a);
        for (size_t i = 0; i < 2; i++)
        {
          if (as[i].isVar() && !expr::hasSubterm(as[1-i], as[i]))
          {
            s.add(as[i], as[1 - i]);
            // this equality is definitely relevant
            blockers.insert(a);
            continue;
          }
        }
      }
      // otherwise, it may be relevant below
      possible.push_back(a);
    }
    // do not add blockers that are implied by the substitution
    for (const Node& a : possible)
    {
      Node as = rewrite(s.apply(a));
      if (as.isConst())
      {
        continue;
      }
      blockers.insert(a);
    }
  }
  if (isOutputOn(OutputTag::BLOCK_MODEL))
  {
    std::vector<Node> bvec(blockers.begin(), blockers.end());
    Node bu = nm->mkAnd(bvec);
    output(OutputTag::BLOCK_MODEL)
        << "(block-model " << bu << ")" << std::endl;
  }
  // go back and erase the trivial blockers
  for (const Node& bt : blockersTriv)
  {
    blockers.erase(bt);
  }
  std::vector<Node> bvec(blockers.begin(), blockers.end());
  Node blocker = nm->mkAnd(bvec).notNode();
  Trace("model-blocker") << "...model blocker is " << blocker << std::endl;
  return blocker;
}

}  // namespace cvc5::internal

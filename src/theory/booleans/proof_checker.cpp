/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equality proof checker.
 */

#include "theory/booleans/proof_checker.h"
#include "expr/skolem_manager.h"
#include "theory/rewriter.h"

namespace cvc5 {
namespace theory {
namespace booleans {

void BoolProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::SPLIT, this);
  pc->registerChecker(PfRule::RESOLUTION, this);
  pc->registerChecker(PfRule::CHAIN_RESOLUTION, this);
  pc->registerTrustedChecker(PfRule::MACRO_RESOLUTION_TRUST, this, 3);
  pc->registerChecker(PfRule::MACRO_RESOLUTION, this);
  pc->registerChecker(PfRule::FACTORING, this);
  pc->registerChecker(PfRule::REORDERING, this);
  pc->registerChecker(PfRule::EQ_RESOLVE, this);
  pc->registerChecker(PfRule::MODUS_PONENS, this);
  pc->registerChecker(PfRule::NOT_NOT_ELIM, this);
  pc->registerChecker(PfRule::CONTRA, this);
  pc->registerChecker(PfRule::AND_ELIM, this);
  pc->registerChecker(PfRule::AND_INTRO, this);
  pc->registerChecker(PfRule::NOT_OR_ELIM, this);
  pc->registerChecker(PfRule::IMPLIES_ELIM, this);
  pc->registerChecker(PfRule::NOT_IMPLIES_ELIM1, this);
  pc->registerChecker(PfRule::NOT_IMPLIES_ELIM2, this);
  pc->registerChecker(PfRule::EQUIV_ELIM1, this);
  pc->registerChecker(PfRule::EQUIV_ELIM2, this);
  pc->registerChecker(PfRule::NOT_EQUIV_ELIM1, this);
  pc->registerChecker(PfRule::NOT_EQUIV_ELIM2, this);
  pc->registerChecker(PfRule::XOR_ELIM1, this);
  pc->registerChecker(PfRule::XOR_ELIM2, this);
  pc->registerChecker(PfRule::NOT_XOR_ELIM1, this);
  pc->registerChecker(PfRule::NOT_XOR_ELIM2, this);
  pc->registerChecker(PfRule::ITE_ELIM1, this);
  pc->registerChecker(PfRule::ITE_ELIM2, this);
  pc->registerChecker(PfRule::NOT_ITE_ELIM1, this);
  pc->registerChecker(PfRule::NOT_ITE_ELIM2, this);
  pc->registerChecker(PfRule::NOT_AND, this);
  pc->registerChecker(PfRule::CNF_AND_POS, this);
  pc->registerChecker(PfRule::CNF_AND_NEG, this);
  pc->registerChecker(PfRule::CNF_OR_POS, this);
  pc->registerChecker(PfRule::CNF_OR_NEG, this);
  pc->registerChecker(PfRule::CNF_IMPLIES_POS, this);
  pc->registerChecker(PfRule::CNF_IMPLIES_NEG1, this);
  pc->registerChecker(PfRule::CNF_IMPLIES_NEG2, this);
  pc->registerChecker(PfRule::CNF_EQUIV_POS1, this);
  pc->registerChecker(PfRule::CNF_EQUIV_POS2, this);
  pc->registerChecker(PfRule::CNF_EQUIV_NEG1, this);
  pc->registerChecker(PfRule::CNF_EQUIV_NEG2, this);
  pc->registerChecker(PfRule::CNF_XOR_POS1, this);
  pc->registerChecker(PfRule::CNF_XOR_POS2, this);
  pc->registerChecker(PfRule::CNF_XOR_NEG1, this);
  pc->registerChecker(PfRule::CNF_XOR_NEG2, this);
  pc->registerChecker(PfRule::CNF_ITE_POS1, this);
  pc->registerChecker(PfRule::CNF_ITE_POS2, this);
  pc->registerChecker(PfRule::CNF_ITE_POS3, this);
  pc->registerChecker(PfRule::CNF_ITE_NEG1, this);
  pc->registerChecker(PfRule::CNF_ITE_NEG2, this);
  pc->registerChecker(PfRule::CNF_ITE_NEG3, this);
  pc->registerTrustedChecker(PfRule::SAT_REFUTATION, this, 1);
}

Node BoolProofRuleChecker::checkInternal(PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  if (id == PfRule::RESOLUTION)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 2);
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> disjuncts;
    Node pivots[2];
    if (args[0] == nm->mkConst(true))
    {
      pivots[0] = args[1];
      pivots[1] = args[1].notNode();
    }
    else
    {
      Assert(args[0] == nm->mkConst(false));
      pivots[0] = args[1].notNode();
      pivots[1] = args[1];
    }
    for (unsigned i = 0; i < 2; ++i)
    {
      // determine whether the clause is a singleton for effects of resolution,
      // which is the case if it's not an OR node or it is an OR node but it is
      // equal to the pivot
      std::vector<Node> lits;
      if (children[i].getKind() == kind::OR && pivots[i] != children[i])
      {
        lits.insert(lits.end(), children[i].begin(), children[i].end());
      }
      else
      {
        lits.push_back(children[i]);
      }
      for (unsigned j = 0, size = lits.size(); j < size; ++j)
      {
        if (pivots[i] != lits[j])
        {
          disjuncts.push_back(lits[j]);
        }
        else
        {
          // just eliminate first occurrence
          pivots[i] = Node::null();
        }
      }
    }
    return disjuncts.empty()
               ? nm->mkConst(false)
               : disjuncts.size() == 1 ? disjuncts[0]
                                       : nm->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::FACTORING)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::OR)
    {
      return Node::null();
    }
    // remove duplicates while keeping the order of children
    std::unordered_set<TNode> clauseSet;
    std::vector<Node> disjuncts;
    unsigned size = children[0].getNumChildren();
    for (unsigned i = 0; i < size; ++i)
    {
      if (clauseSet.count(children[0][i]))
      {
        continue;
      }
      disjuncts.push_back(children[0][i]);
      clauseSet.insert(children[0][i]);
    }
    if (disjuncts.size() == size)
    {
      return Node::null();
    }
    NodeManager* nm = NodeManager::currentNM();
    return disjuncts.empty()
               ? nm->mkConst<bool>(false)
               : disjuncts.size() == 1 ? disjuncts[0]
                                       : nm->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::REORDERING)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    std::unordered_set<Node> clauseSet1, clauseSet2;
    if (children[0].getKind() == kind::OR)
    {
      clauseSet1.insert(children[0].begin(), children[0].end());
    }
    else
    {
      clauseSet1.insert(children[0]);
    }
    if (args[0].getKind() == kind::OR)
    {
      clauseSet2.insert(args[0].begin(), args[0].end());
    }
    else
    {
      clauseSet2.insert(args[0]);
    }
    if (clauseSet1 != clauseSet2)
    {
      Trace("bool-pfcheck") << id << ": clause set1: " << clauseSet1 << "\n"
                            << id << ": clause set2: " << clauseSet2 << "\n";
      return Node::null();
    }
    return args[0];
  }
  if (id == PfRule::CHAIN_RESOLUTION)
  {
    Assert(children.size() > 1);
    Assert(args.size() == 2 * (children.size() - 1));
    Trace("bool-pfcheck") << "chain_res:\n" << push;
    NodeManager* nm = NodeManager::currentNM();
    Node trueNode = nm->mkConst(true);
    Node falseNode = nm->mkConst(false);
    std::vector<Node> clauseNodes;
    // literals to be removed from the virtual lhs clause of the resolution
    std::unordered_map<Node, unsigned> lhsElim;
    for (std::size_t i = 0, argsSize = args.size(); i < argsSize; i = i + 2)
    {
      // whether pivot should occur as is or negated depends on the polarity of
      // each step in the chain
      if (args[i] == trueNode)
      {
        lhsElim[args[i + 1]]++;
      }
      else
      {
        Assert(args[i] == falseNode);
        lhsElim[args[i + 1].notNode()]++;
      }
    }
    if (Trace.isOn("bool-pfcheck"))
    {
      Trace("bool-pfcheck")
          << "Original elimination multiset for lhs clause:\n";
      for (const auto& pair : lhsElim)
      {
        Trace("bool-pfcheck")
            << "\t- " << pair.first << " {" << pair.second << "}\n";
      }
    }
    for (std::size_t i = 0, childrenSize = children.size(); i < childrenSize;
         ++i)
    {
      // literal to be removed from rhs clause. They will be negated
      Node rhsElim = Node::null();
      if (Trace.isOn("bool-pfcheck"))
      {
        Trace("bool-pfcheck") << i << ": current lhsElim:\n";
        for (const auto& pair : lhsElim)
        {
          Trace("bool-pfcheck")
              << "\t- " << pair.first << " {" << pair.second << "}\n";
        }
      }
      if (i > 0)
      {
        std::size_t index = 2 * (i - 1);
        rhsElim = args[index] == trueNode ? args[index + 1].notNode()
                                          : args[index + 1];
        Trace("bool-pfcheck") << i << ": rhs elim: " << rhsElim << "\n";
      }
      // Only add to conclusion nodes that are not in elimination set. First get
      // the nodes.
      //
      // Since a Node cannot hold an OR with a single child we need to
      // disambiguate singleton clauses that are OR nodes from non-singleton
      // clauses (i.e. unit clauses in the SAT solver).
      //
      // If the child is not an OR, it is a singleton clause and we take the
      // child itself as the clause. Otherwise the child can only be a singleton
      // clause if the child itself is used as a resolution literal, i.e. if the
      // child is in lhsElim or is equal to rhsElim (which means that the
      // negation of the child is in lhsElim).
      std::vector<Node> lits;
      if (children[i].getKind() == kind::OR && lhsElim.count(children[i]) == 0
          && children[i] != rhsElim)
      {
        lits.insert(lits.end(), children[i].begin(), children[i].end());
      }
      else
      {
        lits.push_back(children[i]);
      }
      Trace("bool-pfcheck") << i << ": clause lits: " << lits << "\n";
      std::vector<Node> added;
      for (std::size_t j = 0, size = lits.size(); j < size; ++j)
      {
        if (lits[j] == rhsElim)
        {
          rhsElim = Node::null();
          continue;
        }
        auto it = lhsElim.find(lits[j]);
        if (it == lhsElim.end())
        {
          clauseNodes.push_back(lits[j]);
          added.push_back(lits[j]);
        }
        else
        {
          // remove occurrence
          it->second--;
          if (it->second == 0)
          {
            lhsElim.erase(it);
          }
        }
      }
      Trace("bool-pfcheck") << i << ": added lits: " << added << "\n\n";
    }
    Trace("bool-pfcheck") << "clause: " << clauseNodes << "\n" << pop;
    return clauseNodes.empty()
               ? nm->mkConst(false)
               : clauseNodes.size() == 1 ? clauseNodes[0]
                                         : nm->mkNode(kind::OR, clauseNodes);
  }
  if (id == PfRule::MACRO_RESOLUTION_TRUST)
  {
    Assert(children.size() > 1);
    Assert(args.size() == 2 * (children.size() - 1) + 1);
    return args[0];
  }
  if (id == PfRule::MACRO_RESOLUTION)
  {
    Assert(children.size() > 1);
    Assert(args.size() == 2 * (children.size() - 1) + 1);
    Trace("bool-pfcheck") << "macro_res: " << args[0] << "\n" << push;
    NodeManager* nm = NodeManager::currentNM();
    Node trueNode = nm->mkConst(true);
    Node falseNode = nm->mkConst(false);
    std::vector<Node> clauseNodes;
    for (std::size_t i = 0, childrenSize = children.size(); i < childrenSize;
         ++i)
    {
      std::unordered_set<Node> elim;
      // literals to be removed from "first" clause
      if (i < childrenSize - 1)
      {
        for (std::size_t j = (2 * i) + 1, argsSize = args.size(); j < argsSize;
             j = j + 2)
        {
          // whether pivot should occur as is or negated depends on the polarity
          // of each step in the macro
          if (args[j] == trueNode)
          {
            elim.insert(args[j + 1]);
          }
          else
          {
            Assert(args[j] == falseNode);
            elim.insert(args[j + 1].notNode());
          }
        }
      }
      // literal to be removed from "second" clause. They will be negated
      if (i > 0)
      {
        std::size_t index = 2 * (i - 1) + 1;
        Node pivot = args[index] == trueNode ? args[index + 1].notNode()
                                             : args[index + 1];
        elim.insert(pivot);
      }
      Trace("bool-pfcheck") << i << ": elimination set: " << elim << "\n";
      // only add to conclusion nodes that are not in elimination set. First get
      // the nodes.
      //
      // Since a Node cannot hold an OR with a single child we need to
      // disambiguate singleton clauses that are OR nodes from non-singleton
      // clauses (i.e. unit clauses in the SAT solver).
      //
      // If the child is not an OR, it is a singleton clause and we take the
      // child itself as the clause. Otherwise the child can only be a singleton
      // clause if the child itself is used as a resolution literal, i.e. if the
      // child is in lhsElim or is equal to rhsElim (which means that the
      // negation of the child is in lhsElim).
      std::vector<Node> lits;
      if (children[i].getKind() == kind::OR && !elim.count(children[i]))
      {
        lits.insert(lits.end(), children[i].begin(), children[i].end());
      }
      else
      {
        lits.push_back(children[i]);
      }
      Trace("bool-pfcheck") << i << ": clause lits: " << lits << "\n";
      std::vector<Node> added;
      for (std::size_t j = 0, size = lits.size(); j < size; ++j)
      {
        // only add if literal does not occur in elimination set
        if (elim.count(lits[j]) == 0)
        {
          clauseNodes.push_back(lits[j]);
          added.push_back(lits[j]);
          // eliminate duplicates
          elim.insert(lits[j]);
        }
      }
      Trace("bool-pfcheck") << i << ": added lits: " << added << "\n\n";
    }
    Trace("bool-pfcheck") << "clause: " << clauseNodes << "\n";
    // check that set representation is the same as of the given conclusion
    std::unordered_set<Node> clauseComputed{clauseNodes.begin(),
                                            clauseNodes.end()};
    Trace("bool-pfcheck") << "clauseSet: " << clauseComputed << "\n" << pop;
    if (clauseComputed.empty())
    {
      // conclusion differ
      if (args[0] != falseNode)
      {
        return Node::null();
      }
      return args[0];
    }
    if (clauseComputed.size() == 1)
    {
      // conclusion differ
      if (args[0] != *clauseComputed.begin())
      {
        return Node::null();
      }
      return args[0];
    }
    // At this point, should amount to them differing only on order. So the
    // original result can't be a singleton clause
    if (args[0].getKind() != kind::OR
        || clauseComputed.size() != args[0].getNumChildren())
    {
      return Node::null();
    }
    std::unordered_set<Node> clauseGiven{args[0].begin(), args[0].end()};
    return clauseComputed == clauseGiven ? args[0] : Node::null();
  }
  if (id == PfRule::SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return NodeManager::currentNM()->mkNode(
        kind::OR, args[0], args[0].notNode());
  }
  if (id == PfRule::CONTRA)
  {
    Assert(children.size() == 2);
    if (children[1].getKind() == Kind::NOT && children[0] == children[1][0])
    {
      return NodeManager::currentNM()->mkConst(false);
    }
    return Node::null();
  }
  if (id == PfRule::EQ_RESOLVE)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[1].getKind() != kind::EQUAL || children[0] != children[1][0])
    {
      return Node::null();
    }
    return children[1][1];
  }
  if (id == PfRule::MODUS_PONENS)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[1].getKind() != kind::IMPLIES || children[0] != children[1][0])
    {
      return Node::null();
    }
    return children[1][1];
  }
  if (id == PfRule::NOT_NOT_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT || children[0][0].getKind() != kind::NOT)
    {
      return Node::null();
    }
    return children[0][0][0];
  }
  // natural deduction rules
  if (id == PfRule::AND_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != kind::AND || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0].getNumChildren())
    {
      return Node::null();
    }
    return children[0][i];
  }
  if (id == PfRule::AND_INTRO)
  {
    Assert(children.size() >= 1);
    return children.size() == 1
               ? children[0]
               : NodeManager::currentNM()->mkNode(kind::AND, children);
  }
  if (id == PfRule::NOT_OR_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::OR || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0][0].getNumChildren())
    {
      return Node::null();
    }
    return children[0][0][i].notNode();
  }
  if (id == PfRule::IMPLIES_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == PfRule::NOT_IMPLIES_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    return children[0][0][0];
  }
  if (id == PfRule::NOT_IMPLIES_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    return children[0][0][1].notNode();
  }
  if (id == PfRule::EQUIV_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == PfRule::EQUIV_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0], children[0][1].notNode());
  }
  if (id == PfRule::NOT_EQUIV_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0], children[0][0][1]);
  }
  if (id == PfRule::NOT_EQUIV_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0].notNode(), children[0][0][1].notNode());
  }
  if (id == PfRule::XOR_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0], children[0][1]);
  }
  if (id == PfRule::XOR_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0].notNode(), children[0][1].notNode());
  }
  if (id == PfRule::NOT_XOR_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0], children[0][0][1].notNode());
  }
  if (id == PfRule::NOT_XOR_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0].notNode(), children[0][0][1]);
  }
  if (id == PfRule::ITE_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == PfRule::ITE_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0], children[0][2]);
  }
  if (id == PfRule::NOT_ITE_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0].notNode(), children[0][0][1].notNode());
  }
  if (id == PfRule::NOT_ITE_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, children[0][0][0], children[0][0][2].notNode());
  }
  // De Morgan
  if (id == PfRule::NOT_AND)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::AND)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts;
    for (std::size_t i = 0, size = children[0][0].getNumChildren(); i < size;
         ++i)
    {
      disjuncts.push_back(children[0][0][i].notNode());
    }
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  // valid clauses rules for Tseitin CNF transformation
  if (id == PfRule::CNF_AND_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    uint32_t i;
    if (args[0].getKind() != kind::AND || !getUInt32(args[1], i))
    {
      return Node::null();
    }
    if (i >= args[0].getNumChildren())
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, args[0].notNode(), args[0][i]);
  }
  if (id == PfRule::CNF_AND_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::AND)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0]};
    for (unsigned i = 0, size = args[0].getNumChildren(); i < size; ++i)
    {
      disjuncts.push_back(args[0][i].notNode());
    }
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_OR_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::OR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode()};
    for (unsigned i = 0, size = args[0].getNumChildren(); i < size; ++i)
    {
      disjuncts.push_back(args[0][i]);
    }
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_OR_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    uint32_t i;
    if (args[0].getKind() != kind::OR || !getUInt32(args[1], i))
    {
      return Node::null();
    }
    if (i >= args[0].getNumChildren())
    {
      return Node::null();
    }
    return NodeManager::currentNM()->mkNode(
        kind::OR, args[0], args[0][i].notNode());
  }
  if (id == PfRule::CNF_IMPLIES_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_IMPLIES_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_IMPLIES_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_EQUIV_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_EQUIV_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0], args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_EQUIV_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_EQUIV_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][0].notNode(), args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_XOR_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][0], args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_XOR_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_XOR_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0].notNode(), args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_XOR_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][0], args[0][2]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_POS3)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][1], args[0][2]};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][0].notNode(), args[0][1].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][2].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::CNF_ITE_NEG3)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][1].notNode(), args[0][2].notNode()};
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
  }
  if (id == PfRule::SAT_REFUTATION)
  {
    Assert(args.empty());
    return NodeManager::currentNM()->mkConst(false);
  }
  // no rule
  return Node::null();
}

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5

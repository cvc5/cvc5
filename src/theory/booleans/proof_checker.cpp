/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equality proof checker
 **/

#include "theory/booleans/proof_checker.h"

namespace CVC4 {
namespace theory {
namespace booleans {

void BoolProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::SPLIT, this);
  pc->registerChecker(PfRule::RESOLUTION, this);
  pc->registerChecker(PfRule::CHAIN_RESOLUTION, this);
  pc->registerChecker(PfRule::FACTORING, this);
  pc->registerChecker(PfRule::REORDERING, this);
  pc->registerChecker(PfRule::EQ_RESOLVE, this);
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
}

Node BoolProofRuleChecker::checkInternal(PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  if (id == PfRule::RESOLUTION)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 1);
    std::vector<Node> disjuncts;
    for (unsigned i = 0; i < 2; ++i)
    {
      // if first clause, eliminate pivot, otherwise its negation
      Node elim = i == 0 ? args[0] : args[0].notNode();
      for (unsigned j = 0, size = children[i].getNumChildren(); j < size; ++j)
      {
        if (elim != children[i][j])
        {
          disjuncts.push_back(children[i][j]);
        }
      }
    }
    return NodeManager::currentNM()->mkNode(kind::OR, disjuncts);
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
    std::unordered_set<TNode, TNodeHashFunction> clauseSet;
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
    std::unordered_set<Node, NodeHashFunction> clauseSet1, clauseSet2;
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
    Assert(args.size() == children.size() - 1);
    Trace("bool-pfcheck") << "chain_res:\n" << push;
    std::vector<Node> clauseNodes;
    for (unsigned i = 0, childrenSize = children.size(); i < childrenSize; ++i)
    {
      std::unordered_set<Node, NodeHashFunction> elim;
      // literals to be removed from "first" clause
      if (i < childrenSize - 1)
      {
        elim.insert(args.begin() + i, args.end());
      }
      // literal to be removed from "second" clause. They will be negated
      if (i > 0)
      {
        elim.insert(args[i - 1].negate());
      }
      Trace("bool-pfcheck") << i << ": elimination set: " << elim << "\n";
      // only add to conclusion nodes that are not in elimination set. First get
      // the nodes.
      //
      // Since unit clauses can also be OR nodes, we rely on the invariant that
      // non-unit clauses will not occur themselves in their elimination sets.
      // If they do then they must be unit.
      std::vector<Node> lits;
      if (children[i].getKind() == kind::OR && elim.count(children[i]) == 0)
      {
        lits.insert(lits.end(), children[i].begin(), children[i].end());
      }
      else
      {
        lits.push_back(children[i]);
      }
      Trace("bool-pfcheck") << i << ": clause lits: " << lits << "\n";
      std::vector<Node> added;
      for (unsigned j = 0, size = lits.size(); j < size; ++j)
      {
        if (elim.count(lits[j]) == 0)
        {
          clauseNodes.push_back(lits[j]);
          added.push_back(lits[j]);
        }
      }
      Trace("bool-pfcheck") << i << ": added lits: " << added << "\n\n";
    }
    Trace("bool-pfcheck") << "clause: " << clauseNodes << "\n" << pop;
    NodeManager* nm = NodeManager::currentNM();
    return clauseNodes.empty()
               ? nm->mkConst<bool>(false)
               : clauseNodes.size() == 1 ? clauseNodes[0]
                                         : nm->mkNode(kind::OR, clauseNodes);
  }
  if (id == PfRule::SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return NodeManager::currentNM()->mkNode(
        kind::OR, args[0], args[0].notNode());
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
    for (unsigned i = 0, size = children[0][0].getNumChildren(); i < size; ++i)
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
  // no rule
  return Node::null();
}

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

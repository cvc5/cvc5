/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Hans-Joerg Schurr
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {
namespace booleans {

BoolProofRuleChecker::BoolProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void BoolProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::SPLIT, this);
  pc->registerChecker(ProofRule::RESOLUTION, this);
  pc->registerChecker(ProofRule::CHAIN_RESOLUTION, this);
  pc->registerTrustedChecker(ProofRule::MACRO_RESOLUTION_TRUST, this, 3);
  pc->registerChecker(ProofRule::MACRO_RESOLUTION, this);
  pc->registerChecker(ProofRule::CHAIN_M_RESOLUTION, this);
  pc->registerChecker(ProofRule::FACTORING, this);
  pc->registerChecker(ProofRule::REORDERING, this);
  pc->registerChecker(ProofRule::EQ_RESOLVE, this);
  pc->registerChecker(ProofRule::MODUS_PONENS, this);
  pc->registerChecker(ProofRule::NOT_NOT_ELIM, this);
  pc->registerChecker(ProofRule::CONTRA, this);
  pc->registerChecker(ProofRule::AND_ELIM, this);
  pc->registerChecker(ProofRule::AND_INTRO, this);
  pc->registerChecker(ProofRule::NOT_OR_ELIM, this);
  pc->registerChecker(ProofRule::IMPLIES_ELIM, this);
  pc->registerChecker(ProofRule::NOT_IMPLIES_ELIM1, this);
  pc->registerChecker(ProofRule::NOT_IMPLIES_ELIM2, this);
  pc->registerChecker(ProofRule::EQUIV_ELIM1, this);
  pc->registerChecker(ProofRule::EQUIV_ELIM2, this);
  pc->registerChecker(ProofRule::NOT_EQUIV_ELIM1, this);
  pc->registerChecker(ProofRule::NOT_EQUIV_ELIM2, this);
  pc->registerChecker(ProofRule::XOR_ELIM1, this);
  pc->registerChecker(ProofRule::XOR_ELIM2, this);
  pc->registerChecker(ProofRule::NOT_XOR_ELIM1, this);
  pc->registerChecker(ProofRule::NOT_XOR_ELIM2, this);
  pc->registerChecker(ProofRule::ITE_ELIM1, this);
  pc->registerChecker(ProofRule::ITE_ELIM2, this);
  pc->registerChecker(ProofRule::NOT_ITE_ELIM1, this);
  pc->registerChecker(ProofRule::NOT_ITE_ELIM2, this);
  pc->registerChecker(ProofRule::NOT_AND, this);
  pc->registerChecker(ProofRule::CNF_AND_POS, this);
  pc->registerChecker(ProofRule::CNF_AND_NEG, this);
  pc->registerChecker(ProofRule::CNF_OR_POS, this);
  pc->registerChecker(ProofRule::CNF_OR_NEG, this);
  pc->registerChecker(ProofRule::CNF_IMPLIES_POS, this);
  pc->registerChecker(ProofRule::CNF_IMPLIES_NEG1, this);
  pc->registerChecker(ProofRule::CNF_IMPLIES_NEG2, this);
  pc->registerChecker(ProofRule::CNF_EQUIV_POS1, this);
  pc->registerChecker(ProofRule::CNF_EQUIV_POS2, this);
  pc->registerChecker(ProofRule::CNF_EQUIV_NEG1, this);
  pc->registerChecker(ProofRule::CNF_EQUIV_NEG2, this);
  pc->registerChecker(ProofRule::CNF_XOR_POS1, this);
  pc->registerChecker(ProofRule::CNF_XOR_POS2, this);
  pc->registerChecker(ProofRule::CNF_XOR_NEG1, this);
  pc->registerChecker(ProofRule::CNF_XOR_NEG2, this);
  pc->registerChecker(ProofRule::CNF_ITE_POS1, this);
  pc->registerChecker(ProofRule::CNF_ITE_POS2, this);
  pc->registerChecker(ProofRule::CNF_ITE_POS3, this);
  pc->registerChecker(ProofRule::CNF_ITE_NEG1, this);
  pc->registerChecker(ProofRule::CNF_ITE_NEG2, this);
  pc->registerChecker(ProofRule::CNF_ITE_NEG3, this);
  pc->registerTrustedChecker(ProofRule::SAT_REFUTATION, this, 1);
  pc->registerTrustedChecker(ProofRule::DRAT_REFUTATION, this, 1);
  pc->registerTrustedChecker(ProofRule::SAT_EXTERNAL_PROVE, this, 1);
}

Node BoolProofRuleChecker::checkInternal(ProofRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  if (id == ProofRule::RESOLUTION)
  {
    Assert(children.size() == 2);
    Assert(args.size() == 2);
    NodeManager* nm = nodeManager();
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
      if (children[i].getKind() == Kind::OR && pivots[i] != children[i])
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
    return disjuncts.empty()       ? nm->mkConst(false)
           : disjuncts.size() == 1 ? disjuncts[0]
                                   : nm->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::FACTORING)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::OR)
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
    NodeManager* nm = nodeManager();
    return nm->mkOr(disjuncts);
  }
  if (id == ProofRule::REORDERING)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    std::unordered_set<Node> clauseSet1, clauseSet2;
    if (children[0].getKind() == Kind::OR)
    {
      clauseSet1.insert(children[0].begin(), children[0].end());
    }
    else
    {
      clauseSet1.insert(children[0]);
    }
    if (args[0].getKind() == Kind::OR)
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
  if (id == ProofRule::CHAIN_RESOLUTION)
  {
    Assert(children.size() > 1);
    Assert(args.size() == 2);
    Assert(args[0].getNumChildren() == (children.size() - 1));
    Assert(args[1].getNumChildren() == (children.size() - 1));
    Trace("bool-pfcheck") << "chain_res:\n" << push;
    NodeManager* nm = nodeManager();
    Node trueNode = nm->mkConst(true);
    Node falseNode = nm->mkConst(false);
    // The lhs and rhs clauses in a binary resolution step, respectively. Since
    // children correspond to the premises in the resolution chain, the first
    // lhs clause is the first premise, the first rhs clause is the second
    // premise. Each subsequent lhs clause will be the result of the previous
    // binary resolution step in the chain, while each subsequent rhs clause
    // will be respectively the second, third etc premises.
    std::vector<Node> lhsClause, rhsClause;
    // The pivots to be eliminated to the lhs clause and rhs clause in a binary
    // resolution step, respectively
    Node lhsElim, rhsElim;
    // Get lhsClause of first resolution.
    //
    // Since a Node cannot hold an OR with a single child we need to
    // disambiguate singleton clauses that are OR nodes from non-singleton
    // clauses (i.e. unit clauses in the SAT solver).
    //
    // If the child is not an OR, it is a singleton clause and we take the
    // child itself as the clause. Otherwise the child can only be a singleton
    // clause if the child itself is used as a resolution literal, i.e. if the
    // first child equal to the first pivot (which is args[1][0] or
    // args[1][0].notNode() depending on the polarity).
    Node pols = args[0];
    Node lits = args[1];
    if (children[0].getKind() != Kind::OR
        || (pols[0] == trueNode && children[0] == lits[0])
        || (pols[0] == falseNode && children[0] == lits[0].notNode()))
    {
      lhsClause.push_back(children[0]);
    }
    else
    {
      lhsClause.insert(lhsClause.end(), children[0].begin(), children[0].end());
    }
    // Traverse the links, which amounts to for each pair of args removing a
    // literal from the lhs and a literal from the lhs.
    for (size_t i = 0, argsSize = pols.getNumChildren(); i < argsSize; i++)
    {
      // Polarity determines how the pivot occurs in lhs and rhs
      if (pols[i] == trueNode)
      {
        lhsElim = lits[i];
        rhsElim = lits[i].notNode();
      }
      else
      {
        Assert(pols[i] == falseNode);
        lhsElim = lits[i].notNode();
        rhsElim = lits[i];
      }
      // The index of the child corresponding to the current rhs clause
      size_t childIndex = i + 1;
      // Get rhs clause. It's a singleton if not an OR node or if equal to
      // rhsElim
      if (children[childIndex].getKind() != Kind::OR
          || children[childIndex] == rhsElim)
      {
        rhsClause.push_back(children[childIndex]);
      }
      else
      {
        rhsClause = {children[childIndex].begin(), children[childIndex].end()};
      }
      Trace("bool-pfcheck") << i << "-th res link:\n";
      Trace("bool-pfcheck") << "\t - lhsClause: " << lhsClause << "\n";
      Trace("bool-pfcheck") << "\t\t - lhsElim: " << lhsElim << "\n";
      Trace("bool-pfcheck") << "\t - rhsClause: " << rhsClause << "\n";
      Trace("bool-pfcheck") << "\t\t - rhsElim: " << rhsElim << "\n";
      // Compute the resulting clause, which will be the next lhsClause, as
      // follows:
      //   - remove lhsElim from lhsClause
      //   - remove rhsElim from rhsClause and add the lits to lhsClause
      auto itlhs = std::find(lhsClause.begin(), lhsClause.end(), lhsElim);
      AlwaysAssert(itlhs != lhsClause.end());
      lhsClause.erase(itlhs);
      Trace("bool-pfcheck") << "\t.. after lhsClause: " << lhsClause << "\n";
      auto itrhs = std::find(rhsClause.begin(), rhsClause.end(), rhsElim);
      AlwaysAssert(itrhs != rhsClause.end());
      lhsClause.insert(lhsClause.end(), rhsClause.begin(), itrhs);
      lhsClause.insert(lhsClause.end(), itrhs + 1, rhsClause.end());
      if (TraceIsOn("bool-pfcheck"))
      {
        std::vector<Node> updatedRhsClause{rhsClause.begin(), itrhs};
        updatedRhsClause.insert(
            updatedRhsClause.end(), itrhs + 1, rhsClause.end());
        Trace("bool-pfcheck")
            << "\t.. after rhsClause: " << updatedRhsClause << "\n";
      }
      rhsClause.clear();
    }
    Trace("bool-pfcheck") << "\n resulting clause: " << lhsClause << "\n"
                          << pop;
    return nm->mkOr(lhsClause);
  }
  if (id == ProofRule::MACRO_RESOLUTION_TRUST)
  {
    Assert(children.size() > 1);
    Assert(args.size() == 2 * (children.size() - 1) + 1);
    return args[0];
  }
  if (id == ProofRule::MACRO_RESOLUTION || id == ProofRule::CHAIN_M_RESOLUTION)
  {
    Assert(children.size() > 1);
    Trace("bool-pfcheck") << "macro_res: " << args[0] << "\n" << push;
    NodeManager* nm = nodeManager();
    Node trueNode = nm->mkConst(true);
    Node falseNode = nm->mkConst(false);
    std::vector<Node> lhsClause, rhsClause;
    Node lhsElim, rhsElim;
    std::vector<Node> pols, lits;
    if (id == ProofRule::MACRO_RESOLUTION)
    {
      Assert(args.size() == 2 * (children.size() - 1) + 1);
      for (size_t i = 1, nargs = args.size(); i < nargs; i = i + 2)
      {
        pols.push_back(args[i]);
        lits.push_back(args[i + 1]);
      }
    }
    else
    {
      Assert(args.size() == 3);
      Assert(id == ProofRule::CHAIN_M_RESOLUTION);
      pols.insert(pols.end(), args[1].begin(), args[1].end());
      lits.insert(lits.end(), args[2].begin(), args[2].end());
    }
    if (children[0].getKind() != Kind::OR
        || (pols[0] == trueNode && children[0] == lits[0])
        || (pols[0] == falseNode && children[0] == lits[0].notNode()))
    {
      lhsClause.push_back(children[0]);
    }
    else
    {
      lhsClause.insert(lhsClause.end(), children[0].begin(), children[0].end());
    }
    // Traverse the links, which amounts to for each pair of args removing a
    // literal from the lhs and a literal from the lhs.
    for (size_t i = 0, argsSize = pols.size(); i < argsSize; i++)
    {
      // Polarity determines how the pivot occurs in lhs and rhs
      if (pols[i] == trueNode)
      {
        lhsElim = lits[i];
        rhsElim = lits[i].notNode();
      }
      else
      {
        Assert(pols[i] == falseNode);
        lhsElim = lits[i].notNode();
        rhsElim = lits[i];
      }
      // The index of the child corresponding to the current rhs clause
      size_t childIndex = i + 1;
      // Get rhs clause. It's a singleton if not an OR node or if equal to
      // rhsElim
      if (children[childIndex].getKind() != Kind::OR
          || children[childIndex] == rhsElim)
      {
        rhsClause.push_back(children[childIndex]);
      }
      else
      {
        rhsClause = {children[childIndex].begin(), children[childIndex].end()};
      }
      Trace("bool-pfcheck") << i << "-th res link:\n";
      Trace("bool-pfcheck") << "\t - lhsClause: " << lhsClause << "\n";
      Trace("bool-pfcheck") << "\t\t - lhsElim: " << lhsElim << "\n";
      Trace("bool-pfcheck") << "\t - rhsClause: " << rhsClause << "\n";
      Trace("bool-pfcheck") << "\t\t - rhsElim: " << rhsElim << "\n";
      // Compute the resulting clause, which will be the next lhsClause, as
      // follows:
      //   - remove all lhsElim from lhsClause
      //   - remove all rhsElim from rhsClause and add the lits to lhsClause
      //
      // Note that to remove the elements from lhsClaus we use the
      // "erase-remove" idiom in C++: the std::remove call shuffles the elements
      // different from lhsElim to the beginning of the container, returning an
      // iterator to the beginning of the "rest" of the container (with
      // occurrences of lhsElim). Then the call to erase removes the range from
      // there to the end. Once C++ 20 is allowed in the cvc5 code base, this
      // could be done with a single call to std::erase.
      lhsClause.erase(std::remove(lhsClause.begin(), lhsClause.end(), lhsElim),
                      lhsClause.end());
      for (const Node& l : rhsClause)
      {
        // only add if literal does not occur in elimination set
        if (rhsElim != l)
        {
          lhsClause.push_back(l);
        }
      }
      rhsClause.clear();
    }

    Trace("bool-pfcheck") << "clause: " << lhsClause << "\n";
    // check that set representation is the same as of the given conclusion
    std::unordered_set<Node> clauseComputed{lhsClause.begin(), lhsClause.end()};
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
    // At this point, should amount to them differing only on order or in
    // repetitions. So the original result can't be a singleton clause.
    if (args[0].getKind() != Kind::OR)
    {
      return Node::null();
    }
    std::unordered_set<Node> clauseGiven{args[0].begin(), args[0].end()};
    return clauseComputed == clauseGiven ? args[0] : Node::null();
  }
  if (id == ProofRule::SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return nodeManager()->mkNode(Kind::OR, args[0], args[0].notNode());
  }
  if (id == ProofRule::CONTRA)
  {
    Assert(children.size() == 2);
    if (children[1].getKind() == Kind::NOT && children[0] == children[1][0])
    {
      return nodeManager()->mkConst(false);
    }
    return Node::null();
  }
  if (id == ProofRule::EQ_RESOLVE)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[1].getKind() != Kind::EQUAL || children[0] != children[1][0])
    {
      return Node::null();
    }
    return children[1][1];
  }
  if (id == ProofRule::MODUS_PONENS)
  {
    Assert(children.size() == 2);
    Assert(args.empty());
    if (children[1].getKind() != Kind::IMPLIES || children[0] != children[1][0])
    {
      return Node::null();
    }
    return children[1][1];
  }
  if (id == ProofRule::NOT_NOT_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::NOT)
    {
      return Node::null();
    }
    return children[0][0][0];
  }
  // natural deduction rules
  if (id == ProofRule::AND_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != Kind::AND || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0].getNumChildren())
    {
      return Node::null();
    }
    return children[0][i];
  }
  if (id == ProofRule::AND_INTRO)
  {
    Assert(children.size() >= 1);
    return children.size() == 1 ? children[0]
                                : nodeManager()->mkNode(Kind::AND, children);
  }
  if (id == ProofRule::NOT_OR_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::OR || !getUInt32(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0][0].getNumChildren())
    {
      return Node::null();
    }
    return children[0][0][i].notNode();
  }
  if (id == ProofRule::IMPLIES_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == ProofRule::NOT_IMPLIES_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    return children[0][0][0];
  }
  if (id == ProofRule::NOT_IMPLIES_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    return children[0][0][1].notNode();
  }
  if (id == ProofRule::EQUIV_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == ProofRule::EQUIV_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0], children[0][1].notNode());
  }
  if (id == ProofRule::NOT_EQUIV_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0], children[0][0][1]);
  }
  if (id == ProofRule::NOT_EQUIV_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0].notNode(), children[0][0][1].notNode());
  }
  if (id == ProofRule::XOR_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(Kind::OR, children[0][0], children[0][1]);
  }
  if (id == ProofRule::XOR_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0].notNode(), children[0][1].notNode());
  }
  if (id == ProofRule::NOT_XOR_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0], children[0][0][1].notNode());
  }
  if (id == ProofRule::NOT_XOR_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0].notNode(), children[0][0][1]);
  }
  if (id == ProofRule::ITE_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0].notNode(), children[0][1]);
  }
  if (id == ProofRule::ITE_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(Kind::OR, children[0][0], children[0][2]);
  }
  if (id == ProofRule::NOT_ITE_ELIM1)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0].notNode(), children[0][0][1].notNode());
  }
  if (id == ProofRule::NOT_ITE_ELIM2)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    return nodeManager()->mkNode(
        Kind::OR, children[0][0][0], children[0][0][2].notNode());
  }
  // De Morgan
  if (id == ProofRule::NOT_AND)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != Kind::NOT
        || children[0][0].getKind() != Kind::AND)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts;
    for (std::size_t i = 0, size = children[0][0].getNumChildren(); i < size;
         ++i)
    {
      disjuncts.push_back(children[0][0][i].notNode());
    }
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  // valid clauses rules for Tseitin CNF transformation
  if (id == ProofRule::CNF_AND_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    uint32_t i;
    if (args[0].getKind() != Kind::AND || !getUInt32(args[1], i))
    {
      return Node::null();
    }
    if (i >= args[0].getNumChildren())
    {
      return Node::null();
    }
    return nodeManager()->mkNode(Kind::OR, args[0].notNode(), args[0][i]);
  }
  if (id == ProofRule::CNF_AND_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::AND)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0]};
    for (unsigned i = 0, size = args[0].getNumChildren(); i < size; ++i)
    {
      disjuncts.push_back(args[0][i].notNode());
    }
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_OR_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::OR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode()};
    for (unsigned i = 0, size = args[0].getNumChildren(); i < size; ++i)
    {
      disjuncts.push_back(args[0][i]);
    }
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_OR_NEG)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    uint32_t i;
    if (args[0].getKind() != Kind::OR || !getUInt32(args[1], i))
    {
      return Node::null();
    }
    if (i >= args[0].getNumChildren())
    {
      return Node::null();
    }
    return nodeManager()->mkNode(Kind::OR, args[0], args[0][i].notNode());
  }
  if (id == ProofRule::CNF_IMPLIES_POS)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_IMPLIES_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_IMPLIES_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::IMPLIES)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_EQUIV_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_EQUIV_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0], args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_EQUIV_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_EQUIV_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][0].notNode(), args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_XOR_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][0], args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_XOR_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_XOR_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0].notNode(), args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_XOR_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::XOR)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_POS1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0].notNode(), args[0][0].notNode(), args[0][1]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_POS2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][0], args[0][2]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_POS3)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0].notNode(), args[0][1], args[0][2]};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_NEG1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][0].notNode(), args[0][1].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_NEG2)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{args[0], args[0][0], args[0][2].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::CNF_ITE_NEG3)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::ITE)
    {
      return Node::null();
    }
    std::vector<Node> disjuncts{
        args[0], args[0][1].notNode(), args[0][2].notNode()};
    return nodeManager()->mkNode(Kind::OR, disjuncts);
  }
  if (id == ProofRule::SAT_REFUTATION || id == ProofRule::DRAT_REFUTATION
      || id == ProofRule::SAT_EXTERNAL_PROVE)
  {
    Assert(args.size()
           == (id == ProofRule::SAT_REFUTATION
                   ? 0
                   : (id == ProofRule::SAT_EXTERNAL_PROVE ? 1 : 2)));
    return nodeManager()->mkConst(false);
  }
  // no rule
  return Node::null();
}

}  // namespace booleans
}  // namespace theory
}  // namespace cvc5::internal

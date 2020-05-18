/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
  pc->registerChecker(PfRule::AND_ELIM, this);
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
}

Node BoolProofRuleChecker::checkInternal(PfRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  if (id == PfRule::SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return NodeManager::currentNM()->mkNode(
        kind::OR, args[0], args[0].notNode());
  }
  if (id == PfRule::AND_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != kind::AND || !getIndex(args[0], i))
    {
      return Node::null();
    }
    if (i >= children[0].getNumChildren())
    {
      return Node::null();
    }
    return children[0][i];
  }
  if (id == PfRule::NOT_OR_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    uint32_t i;
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::OR || !getIndex(args[0], i))
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
  // no rule
  return Node::null();
}

}  // namespace booleans
}  // namespace theory
}  // namespace CVC4

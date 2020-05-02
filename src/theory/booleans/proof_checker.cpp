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

Node BoolProofRuleChecker::check(PfRule id,
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
    if (children[0].getKind() != kind::AND
        || !ProofChecker::unsignedIntBelowBound(args[0],
                                                children[0].getNumChildren()))
    {
      return Node::null();
    }
    unsigned i = args[0].getConst<Rational>().getNumerator().toUnsignedInt();
    return children[0][i];
  }
  if (id == PfRule::NOT_OR_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    if (children[0].getKind() != kind::NOT
        || children[0][0].getKind() != kind::AND)
    {
      return Node::null();
    }
    unsigned i = args[0].getConst<Rational>().getNumerator().toUnsignedInt();
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

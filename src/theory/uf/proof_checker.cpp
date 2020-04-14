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

#include "theory/uf/proof_checker.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

Node EqProofStepChecker::applySubstitution(Node n, const std::vector<Node>& exp)
{
  Node curr = n;
  // apply substitution one at a time
  for (const Node& eqp : exp)
  {
    if (eqp.isNull() || eqp.getKind() != EQUAL)
    {
      return Node::null();
    }
    TNode var = eqp[0];
    TNode subs = eqp[1];
    curr = curr.substitute(var, subs);
  }
  return curr;
}

Node EqProofStepChecker::check(
    ProofStep id,
    const std::vector<std::shared_ptr<ProofNode>>& children,
    const std::vector<Node>& args)
{
  // compute what was proven
  if (id == ProofStep::ASSUME)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return args[0];
  }
  else if (id == ProofStep::SUBS)
  {
    Assert(children.size() > 0);
    Assert(args.size() == 1);
    std::vector<Node> exp;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      exp.push_back(children[i]->getResult());
    }
    Node res = applySubstitution(args[0], exp);
    return args[0].eqNode(res);
  }
  else if (id == ProofStep::REWRITE)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node res = Rewriter::rewrite(args[0]);
    return args[0].eqNode(res);
  }
  else if (id == ProofStep::REFL)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return args[0].eqNode(args[0]);
  }
  else if (id == ProofStep::SYMM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node eqp = children[0]->getResult();
    if (eqp.isNull() || eqp.getKind() != EQUAL)
    {
      return Node::null();
    }
    return eqp[1].eqNode(eqp[0]);
  }
  else if (id == ProofStep::TRANS)
  {
    Assert(children.size() > 0);
    Assert(args.empty());
    Node first;
    Node curr;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      Node eqp = children[i]->getResult();
      if (eqp.isNull() || eqp.getKind() != EQUAL)
      {
        return Node::null();
      }
      if (first.isNull())
      {
        first = eqp[0];
      }
      else if (eqp[0] != curr)
      {
        return Node::null();
      }
      curr = eqp[1];
    }
    return first.eqNode(curr);
  }
  else if (id == ProofStep::SPLIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return NodeManager::currentNM()->mkNode(OR, args[0], args[0].notNode());
  }
  // no rule
  return Node::null();
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

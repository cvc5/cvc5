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

//#include "theory/builtin/proof_checker.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

Node EqProofRuleChecker::check(PfRule id,
                               const std::vector<Node>& children,
                               const std::vector<Node>& args)
{
  // compute what was proven
  if (id == PfRule::REFL)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    return args[0].eqNode(args[0]);
  }
  else if (id == PfRule::SYMM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node eqp = children[0];
    if (eqp.getKind() != EQUAL)
    {
      return Node::null();
    }
    return eqp[1].eqNode(eqp[0]);
  }
  else if (id == PfRule::TRANS)
  {
    Assert(children.size() > 0);
    Assert(args.empty());
    Node first;
    Node curr;
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      Node eqp = children[i];
      if (eqp.getKind() != EQUAL)
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
  else if (id == PfRule::CONG)
  {
    Assert(children.size() > 0);
    Assert(args.size() == 1);
    // We could handle builtin operators here using
    // kindToOperator/operatorToKind, for now, hard-coded to APPLY_UF
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    lchildren.push_back(args[0]);
    rchildren.push_back(args[0]);
    for (size_t i = 0, nchild = children.size(); i < nchild; i++)
    {
      Node eqp = children[i];
      if (eqp.getKind() != EQUAL)
      {
        return Node::null();
      }
      lchildren.push_back(eqp[0]);
      rchildren.push_back(eqp[1]);
    }
    NodeManager * nm = NodeManager::currentNM();
    Node l = nm->mkNode(APPLY_UF, lchildren);
    Node r = nm->mkNode(APPLY_UF, rchildren);
    return l.eqNode(r);
  }
  else if (id == PfRule::TRUE_INTRO)
  {
    Assert(children.size()==1);
    Assert(args.empty());
    Node trueNode = NodeManager::currentNM()->mkConst(true);
    return children[0].eqNode(trueNode);
  }
  else if (id == PfRule::TRUE_ELIM)
  {
    Assert(children.size()==1);
    Assert(args.empty());
    if (children[0].getKind()!=EQUAL || !children[0][1].isConst())
    {
      
    }
  }
  // no rule
  return Node::null();
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

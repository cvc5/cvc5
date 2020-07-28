/*********************                                                        */
/*! \file proof_checker.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equality proof checker
 **/

#include "theory/uf/proof_checker.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace uf {

void UfProofRuleChecker::registerTo(ProofChecker* pc)
{
  // add checkers
  pc->registerChecker(PfRule::REFL, this);
  pc->registerChecker(PfRule::SYMM, this);
  pc->registerChecker(PfRule::TRANS, this);
  pc->registerChecker(PfRule::CONG, this);
  pc->registerChecker(PfRule::TRUE_INTRO, this);
  pc->registerChecker(PfRule::TRUE_ELIM, this);
  pc->registerChecker(PfRule::FALSE_INTRO, this);
  pc->registerChecker(PfRule::FALSE_ELIM, this);
}

Node UfProofRuleChecker::checkInternal(PfRule id,
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
    bool polarity = children[0].getKind() != NOT;
    Node eqp = polarity ? children[0] : children[0][0];
    if (eqp.getKind() != EQUAL)
    {
      // not a (dis)equality
      return Node::null();
    }
    Node conc = eqp[1].eqNode(eqp[0]);
    return polarity ? conc : conc.notNode();
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
    // We do congruence over builtin kinds using operatorToKind
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    // get the expected kind for args[0]
    Kind k = NodeManager::getKindForFunction(args[0]);
    if (k == kind::UNDEFINED_KIND)
    {
      k = NodeManager::operatorToKind(args[0]);
    }
    if (k == kind::UNDEFINED_KIND)
    {
      return Node::null();
    }
    Trace("uf-pfcheck") << "congruence for " << args[0] << " uses kind " << k
                        << ", metakind=" << kind::metaKindOf(k) << std::endl;
    if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
    {
      // parameterized kinds require the operator
      lchildren.push_back(args[0]);
      rchildren.push_back(args[0]);
    }
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
    NodeManager* nm = NodeManager::currentNM();
    Node l = nm->mkNode(k, lchildren);
    Node r = nm->mkNode(k, rchildren);
    return l.eqNode(r);
  }
  else if (id == PfRule::TRUE_INTRO)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node trueNode = NodeManager::currentNM()->mkConst(true);
    return children[0].eqNode(trueNode);
  }
  else if (id == PfRule::TRUE_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != EQUAL || !children[0][1].isConst()
        || !children[0][1].getConst<bool>())
    {
      return Node::null();
    }
    return children[0][0];
  }
  else if (id == PfRule::FALSE_INTRO)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != kind::NOT)
    {
      return Node::null();
    }
    Node falseNode = NodeManager::currentNM()->mkConst(false);
    return children[0][0].eqNode(falseNode);
  }
  else if (id == PfRule::FALSE_ELIM)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    if (children[0].getKind() != EQUAL || !children[0][1].isConst()
        || children[0][1].getConst<bool>())
    {
      return Node::null();
    }
    return children[0][0].notNode();
  }
  // no rule
  return Node::null();
}

}  // namespace uf
}  // namespace theory
}  // namespace CVC4

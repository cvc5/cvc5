/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of equality proof checker.
 */

#include "theory/uf/proof_checker.h"

#include "theory/uf/theory_uf_rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
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
  pc->registerChecker(PfRule::HO_CONG, this);
  pc->registerChecker(PfRule::HO_APP_ENCODE, this);
  pc->registerChecker(PfRule::BETA_REDUCE, this);
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
    Assert(args.size() >= 1 && args.size() <= 2);
    // We do congruence over builtin kinds using operatorToKind
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    // get the kind encoded as args[0]
    Kind k;
    if (!getKind(args[0], k))
    {
      return Node::null();
    }
    if (k == kind::UNDEFINED_KIND)
    {
      return Node::null();
    }
    Trace("uf-pfcheck") << "congruence for " << args[0] << " uses kind " << k
                        << ", metakind=" << kind::metaKindOf(k) << std::endl;
    if (kind::metaKindOf(k) == kind::metakind::PARAMETERIZED)
    {
      if (args.size() <= 1)
      {
        return Node::null();
      }
      // parameterized kinds require the operator
      lchildren.push_back(args[1]);
      rchildren.push_back(args[1]);
    }
    else if (args.size() > 1)
    {
      return Node::null();
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
  if (id == PfRule::HO_CONG)
  {
    Assert(children.size() > 0);
    std::vector<Node> lchildren;
    std::vector<Node> rchildren;
    for (size_t i = 0, nchild = children.size(); i < nchild; ++i)
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
    Node l = nm->mkNode(kind::APPLY_UF, lchildren);
    Node r = nm->mkNode(kind::APPLY_UF, rchildren);
    return l.eqNode(r);
  }
  else if (id == PfRule::HO_APP_ENCODE)
  {
    Assert(args.size() == 1);
    Node ret = TheoryUfRewriter::getHoApplyForApplyUf(args[0]);
    return args[0].eqNode(ret);
  }
  else if (id == PfRule::BETA_REDUCE)
  {
    Assert(args.size() >= 2);
    Node lambda = args[0];
    if (lambda.getKind() != LAMBDA)
    {
      return Node::null();
    }
    std::vector<TNode> vars(lambda[0].begin(), lambda[0].end());
    std::vector<TNode> subs(args.begin() + 1, args.end());
    if (vars.size() != subs.size())
    {
      return Node::null();
    }
    NodeManager* nm = NodeManager::currentNM();
    std::vector<Node> appArgs;
    appArgs.push_back(lambda);
    appArgs.insert(appArgs.end(), subs.begin(), subs.end());
    Node app = nm->mkNode(APPLY_UF, appArgs);
    Node ret = lambda[1].substitute(
        vars.begin(), vars.end(), subs.begin(), subs.end());
    return app.eqNode(ret);
  }
  // no rule
  return Node::null();
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

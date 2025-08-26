/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of sets proof checker.
 */

#include "theory/sets/proof_checker.h"

#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace theory {
namespace sets {

SetsProofRuleChecker::SetsProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void SetsProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::SETS_SINGLETON_INJ, this);
  pc->registerChecker(ProofRule::SETS_EXT, this);
  pc->registerChecker(ProofRule::SETS_FILTER_UP, this);
  pc->registerChecker(ProofRule::SETS_FILTER_DOWN, this);
}

Node SetsProofRuleChecker::checkInternal(ProofRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  if (id == ProofRule::SETS_SINGLETON_INJ)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node eq = children[0];
    if (eq.getKind() != Kind::EQUAL || eq[0].getKind() != Kind::SET_SINGLETON
        || eq[1].getKind() != Kind::SET_SINGLETON)
    {
      return Node::null();
    }
    return eq[0][0].eqNode(eq[1][0]);
  }
  else if (id == ProofRule::SETS_EXT)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node deq = children[0];
    if (deq.getKind() != Kind::NOT || deq[0].getKind() != Kind::EQUAL
        || !deq[0][0].getType().isSet())
    {
      return Node::null();
    }
    Node a = deq[0][0];
    Node b = deq[0][1];
    SkolemManager* sm = nm->getSkolemManager();
    Node k = sm->mkSkolemFunction(SkolemId::SETS_DEQ_DIFF, {a, b});
    Node as = nm->mkNode(Kind::SET_MEMBER, k, a);
    Node bs = nm->mkNode(Kind::SET_MEMBER, k, b);
    return as.eqNode(bs).notNode();
  }
  else if (id == ProofRule::SETS_FILTER_UP)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    Node mem = children[0];
    if (mem.getKind() != Kind::SET_MEMBER)
    {
      return Node::null();
    }
    Node pred = nm->mkNode(Kind::APPLY_UF, args[0], mem[0]);
    Node filter = nm->mkNode(Kind::SET_FILTER, args[0], mem[1]);
    Node nmem = nm->mkNode(Kind::SET_MEMBER, mem[0], filter);
    return nmem.eqNode(pred);
  }
  else if (id == ProofRule::SETS_FILTER_DOWN)
  {
    Assert(children.size() == 1);
    Node mem = children[0];
    if (mem.getKind() != Kind::SET_MEMBER
        || mem[1].getKind() != Kind::SET_FILTER)
    {
      return Node::null();
    }
    Node nmem = nm->mkNode(Kind::SET_MEMBER, mem[0], mem[1][1]);
    Node pred = nm->mkNode(Kind::APPLY_UF, mem[1][0], mem[0]);
    return nm->mkNode(Kind::AND, nmem, pred);
  }
  // no rule
  return Node::null();
}

}  // namespace sets
}  // namespace theory
}  // namespace cvc5::internal

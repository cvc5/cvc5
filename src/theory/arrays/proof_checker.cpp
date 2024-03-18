/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of arrays proof checker.
 */

#include "theory/arrays/proof_checker.h"

#include "expr/skolem_manager.h"
#include "theory/arrays/skolem_cache.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arrays {

ArraysProofRuleChecker::ArraysProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}
void ArraysProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::ARRAYS_READ_OVER_WRITE, this);
  pc->registerChecker(ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA, this);
  pc->registerChecker(ProofRule::ARRAYS_READ_OVER_WRITE_1, this);
  pc->registerChecker(ProofRule::ARRAYS_EXT, this);
  pc->registerChecker(ProofRule::ARRAYS_EQ_RANGE_EXPAND, this);
}

Node ArraysProofRuleChecker::checkInternal(ProofRule id,
                                           const std::vector<Node>& children,
                                           const std::vector<Node>& args)
{
  NodeManager* nm = NodeManager::currentNM();
  if (id == ProofRule::ARRAYS_READ_OVER_WRITE)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    Node ideq = children[0];
    if (ideq.getKind() != Kind::NOT || ideq[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Node lhs = args[0];
    if (lhs.getKind() != Kind::SELECT || lhs[0].getKind() != Kind::STORE
        || lhs[0][1] != ideq[0][0])
    {
      return Node::null();
    }
    Node rhs = nm->mkNode(Kind::SELECT, lhs[0][0], ideq[0][1]);
    return lhs.eqNode(rhs);
  }
  else if (id == ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node adeq = children[0];
    if (adeq.getKind() != Kind::NOT || adeq[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Node lhs = adeq[0][0];
    Node rhs = adeq[0][1];
    if (lhs.getKind() != Kind::SELECT || lhs[0].getKind() != Kind::STORE
        || rhs.getKind() != Kind::SELECT || lhs[1] != rhs[1])
    {
      return Node::null();
    }
    return lhs[1].eqNode(lhs[0][1]);
  }
  if (id == ProofRule::ARRAYS_READ_OVER_WRITE_1)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node lhs = args[0];
    if (lhs.getKind() != Kind::SELECT || lhs[0].getKind() != Kind::STORE
        || lhs[0][1] != lhs[1])
    {
      return Node::null();
    }
    Node rhs = lhs[0][2];
    return lhs.eqNode(rhs);
  }
  if (id == ProofRule::ARRAYS_EXT)
  {
    Assert(children.size() == 1);
    Assert(args.empty());
    Node adeq = children[0];
    if (adeq.getKind() != Kind::NOT || adeq[0].getKind() != Kind::EQUAL
        || !adeq[0][0].getType().isArray())
    {
      return Node::null();
    }
    Node k = SkolemCache::getExtIndexSkolem(adeq);
    Node a = adeq[0][0];
    Node b = adeq[0][1];
    Node as = nm->mkNode(Kind::SELECT, a, k);
    Node bs = nm->mkNode(Kind::SELECT, b, k);
    return as.eqNode(bs).notNode();
  }
  if (id == ProofRule::ARRAYS_EQ_RANGE_EXPAND)
  {
    Node expandedEqRange = TheoryArraysRewriter::expandEqRange(args[0]);
    return args[0].eqNode(expandedEqRange);
  }
  // no rule
  return Node::null();
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

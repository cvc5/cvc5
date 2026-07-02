/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the Pow2 proof checker.
 */

#include "theory/arith/nl/pow2_proof_checker.h"

#include "theory/arith/arith_utilities.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

Pow2ProofRuleChecker::Pow2ProofRuleChecker(NodeManager* nm)
    : ProofRuleChecker(nm)
{
}

void Pow2ProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(ProofRule::ARITH_POW2_INIT, this);
  pc->registerChecker(ProofRule::ARITH_POW2_MONOTONE, this);
  pc->registerChecker(ProofRule::ARITH_POW2_DIV0, this);
  pc->registerChecker(ProofRule::ARITH_POW2_LOWER_BOUND, this);
}

Node Pow2ProofRuleChecker::checkInternal(
    ProofRule id,
    [[maybe_unused]] const std::vector<Node>& children,
    const std::vector<Node>& args)
{
  NodeManager* nm = nodeManager();
  Node zero = nm->mkConstInt(Rational(0));
  Node two = nm->mkConstInt(Rational(2));
  if (id == ProofRule::ARITH_POW2_INIT)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = args[0];
    if (!t.getType().isInteger())
    {
      return Node::null();
    }
    Node pt = nm->mkNode(Kind::POW2, t);
    Node nonneg = nm->mkNode(Kind::IMPLIES,
                             nm->mkNode(Kind::GEQ, t, zero),
                             nm->mkNode(Kind::GT, pt, zero));
    Node even = nm->mkNode(
        Kind::IMPLIES,
        nm->mkNode(Kind::DISTINCT, t, zero),
        nm->mkNode(Kind::EQUAL, nm->mkNode(Kind::INTS_MODULUS, pt, two), zero));
    Node neg = nm->mkNode(Kind::IMPLIES,
                          nm->mkNode(Kind::LT, t, zero),
                          nm->mkNode(Kind::EQUAL, pt, zero));
    return nm->mkNode(Kind::AND, nonneg, even, neg);
  }
  else if (id == ProofRule::ARITH_POW2_MONOTONE)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Node x = args[0];
    Node y = args[1];
    if (!x.getType().isInteger() || !y.getType().isInteger())
    {
      return Node::null();
    }
    Node assumption = nm->mkNode(
        Kind::AND, nm->mkNode(Kind::LEQ, zero, x), nm->mkNode(Kind::LT, x, y));
    Node conclusion = nm->mkNode(
        Kind::LT, nm->mkNode(Kind::POW2, x), nm->mkNode(Kind::POW2, y));
    return nm->mkNode(Kind::IMPLIES, assumption, conclusion);
  }
  else if (id == ProofRule::ARITH_POW2_DIV0)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Node t = args[0];
    if (!t.getType().isInteger())
    {
      return Node::null();
    }
    Node pt = nm->mkNode(Kind::POW2, t);
    Node div = nm->mkNode(Kind::INTS_DIVISION, t, pt);
    return nm->mkNode(Kind::IMPLIES,
                      nm->mkNode(Kind::GEQ, t, zero),
                      nm->mkNode(Kind::EQUAL, div, zero));
  }
  else if (id == ProofRule::ARITH_POW2_LOWER_BOUND)
  {
    Assert(children.empty());
    Assert(args.size() == 2);
    Node t = args[0];
    Node k = args[1];
    if (!t.getType().isInteger() || !k.getType().isInteger() || !k.isConst())
    {
      return Node::null();
    }
    Node pt = nm->mkNode(Kind::POW2, t);
    Node seven = nm->mkConstInt(Rational(7));
    Node assumption = nm->mkNode(Kind::AND,
                                 nm->mkNode(Kind::GEQ, t, k),
                                 nm->mkNode(Kind::GEQ, k, seven));
    Node kt = nm->mkNode(Kind::MULT, k, t);
    Node kk = nm->mkNode(Kind::MULT, k, k);
    Node bound = nm->mkNode(Kind::ADD, kt, kk);
    return nm->mkNode(
        Kind::IMPLIES, assumption, nm->mkNode(Kind::GT, pt, bound));
  }
  return Node::null();
}

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

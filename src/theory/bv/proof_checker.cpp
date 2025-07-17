/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Abdalrhman Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vectors proof checker.
 */

#include "theory/bv/proof_checker.h"

#include "theory/arith/arith_poly_norm.h"
#include "theory/bv/theory_bv_utils.h"
#include "util/bitvector.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

BVProofRuleChecker::BVProofRuleChecker(NodeManager* nm) : ProofRuleChecker(nm)
{
}
void BVProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerTrustedChecker(ProofRule::MACRO_BV_BITBLAST, this, 2);
  pc->registerChecker(ProofRule::BV_BITBLAST_STEP, this);
  pc->registerChecker(ProofRule::BV_POLY_NORM, this);
  pc->registerChecker(ProofRule::BV_POLY_NORM_EQ, this);
  pc->registerChecker(ProofRule::BV_EAGER_ATOM, this);
}

Node BVProofRuleChecker::checkInternal(ProofRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == ProofRule::MACRO_BV_BITBLAST)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_BITBLAST_STEP)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::EQUAL);
    return args[0];
  }
  else if (id == ProofRule::BV_EAGER_ATOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == Kind::BITVECTOR_EAGER_ATOM);
    return args[0].eqNode(args[0][0]);
  }
  else if (id == ProofRule::BV_POLY_NORM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL || !args[0][0].getType().isBitVector())
    {
      return Node::null();
    }
    if (!arith::PolyNorm::isArithPolyNorm(args[0][0], args[0][1]))
    {
      return Node::null();
    }
    return args[0];
  }
  else if (id == ProofRule::BV_POLY_NORM_EQ)
  {
    Assert(children.size() == 1);
    Assert(args.size() == 1);
    if (args[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Kind k = args[0][0].getKind();
    if (k != Kind::EQUAL)
    {
      return Node::null();
    }
    if (children[0].getKind() != Kind::EQUAL)
    {
      return Node::null();
    }
    Node l = children[0][0];
    Node r = children[0][1];
    if (l.getKind() != Kind::BITVECTOR_MULT || r.getKind() != Kind::BITVECTOR_MULT)
    {
      return Node::null();
    }
    Node cx = l[0];
    Node lr = l[1];
    Node cy = r[0];
    Node rr = r[1];
    if (lr.getKind() != Kind::BITVECTOR_SUB
        || rr.getKind() != Kind::BITVECTOR_SUB)
    {
      return Node::null();
    }
    if (cx.getKind() == Kind::CONST_BITVECTOR
        && cy.getKind() == Kind::CONST_BITVECTOR)
    {
      // must be odd
      if (!bv::utils::getBit(cx, 0) || !bv::utils::getBit(cy, 0))
      {
        return Node::null();
      }
    }
    else
    {
      return Node::null();
    }
    Node x1 = lr[0];
    Node x2 = lr[1];
    Node y1 = rr[0];
    Node y2 = rr[1];
    NodeManager* nm = nodeManager();
    Node ret = nm->mkNode(k, x1, x2).eqNode(nm->mkNode(k, y1, y2));
    if (ret != args[0])
    {
      return Node::null();
    }
    return ret;
  }
  // no rule
  return Node::null();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of bit-vectors proof checker.
 */

#include "theory/bv/proof_checker.h"

namespace cvc5 {
namespace theory {
namespace bv {

void BVProofRuleChecker::registerTo(ProofChecker* pc)
{
  pc->registerChecker(PfRule::BV_BITBLAST, this);
  pc->registerChecker(PfRule::BV_BITBLAST_CONST, this);
  pc->registerChecker(PfRule::BV_BITBLAST_VAR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_EQUAL, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ULT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ULE, this);
  pc->registerChecker(PfRule::BV_BITBLAST_UGT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_UGE, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SLT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SLE, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SGT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SGE, this);
  pc->registerChecker(PfRule::BV_BITBLAST_NOT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_CONCAT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_AND, this);
  pc->registerChecker(PfRule::BV_BITBLAST_OR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_XOR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_XNOR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_NAND, this);
  pc->registerChecker(PfRule::BV_BITBLAST_NOR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_COMP, this);
  pc->registerChecker(PfRule::BV_BITBLAST_MULT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_PLUS, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SUB, this);
  pc->registerChecker(PfRule::BV_BITBLAST_NEG, this);
  pc->registerChecker(PfRule::BV_BITBLAST_UDIV, this);
  pc->registerChecker(PfRule::BV_BITBLAST_UREM, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SDIV, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SREM, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SMOD, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SHL, this);
  pc->registerChecker(PfRule::BV_BITBLAST_LSHR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ASHR, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ULTBV, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SLTBV, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ITE, this);
  pc->registerChecker(PfRule::BV_BITBLAST_EXTRACT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_REPEAT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ZERO_EXTEND, this);
  pc->registerChecker(PfRule::BV_BITBLAST_SIGN_EXTEND, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ROTATE_RIGHT, this);
  pc->registerChecker(PfRule::BV_BITBLAST_ROTATE_LEFT, this);
  pc->registerChecker(PfRule::BV_EAGER_ATOM, this);
}

Node BVProofRuleChecker::checkInternal(PfRule id,
                                       const std::vector<Node>& children,
                                       const std::vector<Node>& args)
{
  if (id == PfRule::BV_BITBLAST)
  {
    BBSimple bb(nullptr);
    Assert(children.empty());
    Assert(args.size() == 1);
    bb.bbAtom(args[0]);
    Node n = bb.getStoredBBAtom(args[0]);
    return args[0].eqNode(n);
  }
  else if (id == PfRule::BV_BITBLAST_CONST || id == PfRule::BV_BITBLAST_VAR
           || id == PfRule::BV_BITBLAST_EQUAL || id == PfRule::BV_BITBLAST_ULT
           || id == PfRule::BV_BITBLAST_ULE || id == PfRule::BV_BITBLAST_UGT
           || id == PfRule::BV_BITBLAST_UGE || id == PfRule::BV_BITBLAST_SLT
           || id == PfRule::BV_BITBLAST_SLE || id == PfRule::BV_BITBLAST_SGT
           || id == PfRule::BV_BITBLAST_SGE || id == PfRule::BV_BITBLAST_NOT
           || id == PfRule::BV_BITBLAST_CONCAT || id == PfRule::BV_BITBLAST_AND
           || id == PfRule::BV_BITBLAST_OR || id == PfRule::BV_BITBLAST_XOR
           || id == PfRule::BV_BITBLAST_XNOR || id == PfRule::BV_BITBLAST_NAND
           || id == PfRule::BV_BITBLAST_NOR || id == PfRule::BV_BITBLAST_COMP
           || id == PfRule::BV_BITBLAST_MULT || id == PfRule::BV_BITBLAST_PLUS
           || id == PfRule::BV_BITBLAST_SUB || id == PfRule::BV_BITBLAST_NEG
           || id == PfRule::BV_BITBLAST_UDIV || id == PfRule::BV_BITBLAST_UREM
           || id == PfRule::BV_BITBLAST_SDIV || id == PfRule::BV_BITBLAST_SREM
           || id == PfRule::BV_BITBLAST_SMOD || id == PfRule::BV_BITBLAST_SHL
           || id == PfRule::BV_BITBLAST_LSHR || id == PfRule::BV_BITBLAST_ASHR
           || id == PfRule::BV_BITBLAST_ULTBV || id == PfRule::BV_BITBLAST_SLTBV
           || id == PfRule::BV_BITBLAST_ITE || id == PfRule::BV_BITBLAST_EXTRACT
           || id == PfRule::BV_BITBLAST_REPEAT
           || id == PfRule::BV_BITBLAST_ZERO_EXTEND
           || id == PfRule::BV_BITBLAST_SIGN_EXTEND
           || id == PfRule::BV_BITBLAST_ROTATE_RIGHT
           || id == PfRule::BV_BITBLAST_ROTATE_LEFT)
  {
    return args[0];
  }
  else if (id == PfRule::BV_EAGER_ATOM)
  {
    Assert(children.empty());
    Assert(args.size() == 1);
    Assert(args[0].getKind() == kind::BITVECTOR_EAGER_ATOM);
    return args[0].eqNode(args[0][0]);
  }
  // no rule
  return Node::null();
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5

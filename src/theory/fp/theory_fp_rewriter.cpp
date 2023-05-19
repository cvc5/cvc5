/******************************************************************************
 * Top contributors (to current version):
 *   Martin Brain, Aina Niemetz, Andres Noetzli
 * Copyright (c) 2013  University of Oxford
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite rules for floating point theories.
 *
 * \todo - Single argument constant propagate / simplify
 *       - Push negations through arithmetic operators (include max and min?
 *         maybe not due to +0/-0)
 *       - classifications to normal tests (maybe)
 *       - (= x (fp.neg x)) --> (isNaN x)
 *       - (fp.eq x (fp.neg x)) --> (isZero x) (previous and reorganise
 *             should be sufficient)
 *       - (fp.eq x const) --> various = depending on const
 *       - (fp.isPositive (fp.neg x)) --> (fp.isNegative x)
 *       - (fp.isNegative (fp.neg x)) --> (fp.isPositive x)
 *       - (fp.isPositive (fp.abs x)) --> (not (isNaN x))
 *       - (fp.isNegative (fp.abs x)) --> false
 *       - A -> castA --> A
 *       - A -> castB -> castC  -->  A -> castC if A <= B <= C
 *       - A -> castB -> castA  -->  A if A <= B
 *       - promotion converts can ignore rounding mode
 *       - Samuel Figuer results
 */

#include "theory/fp/theory_fp_rewriter.h"

#include <algorithm>

#include "base/check.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/fp/fp_word_blaster.h"
#include "util/floatingpoint.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace fp {

namespace rewrite {
  /** Rewrite rules **/
  template <RewriteFunction first, RewriteFunction second>
  RewriteResponse then (TNode node, bool isPreRewrite) {
    RewriteResponse result(first(node, isPreRewrite));

    if (result.d_status == REWRITE_DONE)
    {
      return second(result.d_node, isPreRewrite);
    }
    else
    {
      return result;
    }
  }

  RewriteResponse notFP(TNode node, bool isPreRewrite)
  {
    Unreachable() << "non floating-point kind (" << node.getKind()
                  << ") in floating point rewrite?";
  }

  RewriteResponse identity(TNode node, bool isPreRewrite)
  {
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse type(TNode node, bool isPreRewrite)
  {
    Unreachable() << "sort kind (" << node.getKind()
                  << ") found in expression?";
  }

  RewriteResponse removeDoubleNegation(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
    if (node[0].getKind() == kind::FLOATINGPOINT_NEG) {
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse compactAbs(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_ABS);
    if (node[0].getKind() == kind::FLOATINGPOINT_NEG
        || node[0].getKind() == kind::FLOATINGPOINT_ABS)
    {
      Node ret =
          NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_ABS, node[0][0]);
      return RewriteResponse(REWRITE_AGAIN, ret);
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse convertSubtractionToAddition(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_SUB);
    Node negation = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_NEG,node[2]);
    Node addition = NodeManager::currentNM()->mkNode(
        kind::FLOATINGPOINT_ADD, node[0], node[1], negation);
    return RewriteResponse(REWRITE_DONE, addition);
  }

  RewriteResponse breakChain (TNode node, bool isPreRewrite) {
    Assert(isPreRewrite);  // Should be run first

    Kind k = node.getKind();
    Assert(k == kind::FLOATINGPOINT_EQ || k == kind::FLOATINGPOINT_GEQ
           || k == kind::FLOATINGPOINT_LEQ || k == kind::FLOATINGPOINT_GT
           || k == kind::FLOATINGPOINT_LT);

    size_t children = node.getNumChildren();
    if (children > 2) {
      NodeBuilder conjunction(kind::AND);

      for (size_t i = 0; i < children - 1; ++i) {
	for (size_t j = i + 1; j < children; ++j) {
	  conjunction << NodeManager::currentNM()->mkNode(k, node[i], node[j]);
	}
      }
      return RewriteResponse(REWRITE_AGAIN_FULL, conjunction);

    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }


  /* Implies (fp.eq x x) --> (not (isNaN x))
   */

  RewriteResponse ieeeEqToEq(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_EQ);
    NodeManager *nm = NodeManager::currentNM();

    return RewriteResponse(
        REWRITE_DONE,
        nm->mkNode(
            kind::AND,
            nm->mkNode(
                kind::AND,
                nm->mkNode(kind::NOT,
                           nm->mkNode(kind::FLOATINGPOINT_IS_NAN, node[0])),
                nm->mkNode(kind::NOT,
                           nm->mkNode(kind::FLOATINGPOINT_IS_NAN, node[1]))),
            nm->mkNode(
                kind::OR,
                nm->mkNode(kind::EQUAL, node[0], node[1]),
                nm->mkNode(kind::AND,
                           nm->mkNode(kind::FLOATINGPOINT_IS_ZERO, node[0]),
                           nm->mkNode(kind::FLOATINGPOINT_IS_ZERO, node[1])))));
  }

  RewriteResponse geqToleq(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_GEQ);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LEQ,node[1],node[0]));
  }

  RewriteResponse gtTolt(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_GT);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LT,node[1],node[0]));
  }

  RewriteResponse removed(TNode node, bool isPreRewrite)
  {
    Unreachable() << "kind (" << node.getKind()
                  << ") should have been removed?";
  }

  RewriteResponse variable(TNode node, bool isPreRewrite)
  {
    // We should only get floating point and rounding mode variables to rewrite.
    TypeNode tn = node.getType(true);
    Assert(tn.isFloatingPoint() || tn.isRoundingMode());

    // Not that we do anything with them...
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse equal (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::EQUAL);

    // We should only get equalities of floating point or rounding mode types.
    TypeNode tn = node[0].getType(true);

    Assert(tn.isFloatingPoint() || tn.isRoundingMode());
    Assert(tn
           == node[1].getType(true));  // Should be ensured by the typing rules

    if (node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    } else if (!isPreRewrite && (node[0] > node[1])) {
      Node normal =
          NodeManager::currentNM()->mkNode(kind::EQUAL, node[1], node[0]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }


  // Note these cannot be assumed to be symmetric for +0/-0, thus no symmetry reorder
  RewriteResponse compactMinMax (TNode node, bool isPreRewrite) {
#ifdef CVC5_ASSERTIONS
    Kind k = node.getKind();
    Assert((k == kind::FLOATINGPOINT_MIN) || (k == kind::FLOATINGPOINT_MAX)
           || (k == kind::FLOATINGPOINT_MIN_TOTAL)
           || (k == kind::FLOATINGPOINT_MAX_TOTAL));
#endif
    if (node[0] == node[1]) {
      return RewriteResponse(REWRITE_AGAIN, node[0]);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }


  RewriteResponse reorderFPEquality (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_EQ);
    Assert(!isPreRewrite);  // Likely redundant in pre-rewrite

    if (node[0] > node[1]) {
      Node normal = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_EQ,node[1],node[0]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse reorderBinaryOperation (TNode node, bool isPreRewrite) {
    Kind k = node.getKind();
    Assert((k == kind::FLOATINGPOINT_ADD) || (k == kind::FLOATINGPOINT_MULT));
    Assert(!isPreRewrite);  // Likely redundant in pre-rewrite

    if (node[1] > node[2]) {
      Node normal = NodeManager::currentNM()->mkNode(k,node[0],node[2],node[1]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse reorderFMA (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_FMA);
    Assert(!isPreRewrite);  // Likely redundant in pre-rewrite

    if (node[1] > node[2]) {
      Node normal = NodeManager::currentNM()->mkNode(
          kind::FLOATINGPOINT_FMA, {node[0], node[2], node[1], node[3]});
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse removeSignOperations (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_NORMAL
           || node.getKind() == kind::FLOATINGPOINT_IS_SUBNORMAL
           || node.getKind() == kind::FLOATINGPOINT_IS_ZERO
           || node.getKind() == kind::FLOATINGPOINT_IS_INF
           || node.getKind() == kind::FLOATINGPOINT_IS_NAN);
    Assert(node.getNumChildren() == 1);

    Kind childKind(node[0].getKind());

    if ((childKind == kind::FLOATINGPOINT_NEG) ||
	(childKind == kind::FLOATINGPOINT_ABS)) {

      Node rewritten = NodeManager::currentNM()->mkNode(node.getKind(),node[0][0]);
      return RewriteResponse(REWRITE_AGAIN_FULL, rewritten);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse compactRemainder (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_REM);
    Assert(!isPreRewrite);  // status assumes parts have been rewritten

    Node working = node;

    // (fp.rem (fp.rem X Y) Y) == (fp.rem X Y)
    if (working[0].getKind() == kind::FLOATINGPOINT_REM && // short-cut matters!
	working[0][1] == working[1]) {
      working = working[0];
    }

    // Sign of the RHS does not matter
    if (working[1].getKind() == kind::FLOATINGPOINT_NEG ||
	working[1].getKind() == kind::FLOATINGPOINT_ABS) {
      working[1] = working[1][0];
    }

    // Lift negation out of the LHS so it can be cancelled out
    if (working[0].getKind() == kind::FLOATINGPOINT_NEG) {
      NodeManager * nm = NodeManager::currentNM();
      working = nm->mkNode(
          kind::FLOATINGPOINT_NEG,
          nm->mkNode(kind::FLOATINGPOINT_REM, working[0][0], working[1]));
      // in contrast to other rewrites here, this requires rewrite again full
      return RewriteResponse(REWRITE_AGAIN_FULL, working);
    }

    return RewriteResponse(REWRITE_DONE, working);
  }

  RewriteResponse leqId(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_LEQ);

    if (node[0] == node[1])
    {
      NodeManager *nm = NodeManager::currentNM();
      return RewriteResponse(
          isPreRewrite ? REWRITE_DONE : REWRITE_AGAIN_FULL,
          nm->mkNode(kind::NOT,
                     nm->mkNode(kind::FLOATINGPOINT_IS_NAN, node[0])));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse ltId(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_LT);

    if (node[0] == node[1])
    {
      return RewriteResponse(REWRITE_DONE,
                             NodeManager::currentNM()->mkConst(false));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse toFPSignedBV(TNode node, bool isPreRewrite)
  {
    Assert(!isPreRewrite);
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_SBV);

    /* symFPU does not allow conversions from signed bit-vector of size 1 */
    if (node[1].getType().getBitVectorSize() == 1)
    {
      NodeManager* nm = NodeManager::currentNM();
      Node op = nm->mkConst(FloatingPointToFPUnsignedBitVector(
          node.getOperator().getConst<FloatingPointToFPSignedBitVector>()));
      Node fromubv = nm->mkNode(op, node[0], node[1]);
      return RewriteResponse(
          REWRITE_AGAIN_FULL,
          nm->mkNode(kind::ITE,
                     node[1].eqNode(bv::utils::mkOne(1)),
                     nm->mkNode(kind::FLOATINGPOINT_NEG, fromubv),
                     fromubv));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  };  // namespace rewrite

namespace constantFold {

RewriteResponse fpLiteral(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_FP);

  BitVector bv(node[0].getConst<BitVector>());
  bv = bv.concat(node[1].getConst<BitVector>());
  bv = bv.concat(node[2].getConst<BitVector>());

  // +1 to support the hidden bit
  Node lit = NodeManager::currentNM()->mkConst(
      FloatingPoint(node[1].getConst<BitVector>().getSize(),
                    node[2].getConst<BitVector>().getSize() + 1,
                    bv));

  return RewriteResponse(REWRITE_DONE, lit);
}

RewriteResponse abs(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_ABS);
  Assert(node.getNumChildren() == 1);

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(
                             node[0].getConst<FloatingPoint>().absolute()));
}

RewriteResponse neg(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
  Assert(node.getNumChildren() == 1);

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(
                             node[0].getConst<FloatingPoint>().negate()));
}

RewriteResponse add(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_ADD);
  Assert(node.getNumChildren() == 3);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg1(node[1].getConst<FloatingPoint>());
  FloatingPoint arg2(node[2].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(arg1.add(rm, arg2)));
}

RewriteResponse mult(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MULT);
  Assert(node.getNumChildren() == 3);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg1(node[1].getConst<FloatingPoint>());
  FloatingPoint arg2(node[2].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  return RewriteResponse(
      REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.mult(rm, arg2)));
}

RewriteResponse fma(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_FMA);
  Assert(node.getNumChildren() == 4);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg1(node[1].getConst<FloatingPoint>());
  FloatingPoint arg2(node[2].getConst<FloatingPoint>());
  FloatingPoint arg3(node[3].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());
  Assert(arg1.getSize() == arg3.getSize());

  return RewriteResponse(
      REWRITE_DONE,
      NodeManager::currentNM()->mkConst(arg1.fma(rm, arg2, arg3)));
}

RewriteResponse div(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_DIV);
  Assert(node.getNumChildren() == 3);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg1(node[1].getConst<FloatingPoint>());
  FloatingPoint arg2(node[2].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(arg1.div(rm, arg2)));
}

RewriteResponse sqrt(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_SQRT);
  Assert(node.getNumChildren() == 2);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg(node[1].getConst<FloatingPoint>());

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(arg.sqrt(rm)));
}

RewriteResponse rti(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_RTI);
  Assert(node.getNumChildren() == 2);

  RoundingMode rm(node[0].getConst<RoundingMode>());
  FloatingPoint arg(node[1].getConst<FloatingPoint>());

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(arg.rti(rm)));
}

RewriteResponse rem(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_REM);
  Assert(node.getNumChildren() == 2);

  FloatingPoint arg1(node[0].getConst<FloatingPoint>());
  FloatingPoint arg2(node[1].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  return RewriteResponse(REWRITE_DONE,
                         NodeManager::currentNM()->mkConst(arg1.rem(arg2)));
}

RewriteResponse min(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MIN);
  Assert(node.getNumChildren() == 2);

  FloatingPoint arg1(node[0].getConst<FloatingPoint>());
  FloatingPoint arg2(node[1].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  FloatingPoint::PartialFloatingPoint res(arg1.min(arg2));

  if (res.second)
  {
    Node lit = NodeManager::currentNM()->mkConst(res.first);
    return RewriteResponse(REWRITE_DONE, lit);
  }
  else
  {
    // Can't constant fold the underspecified case
    return RewriteResponse(REWRITE_DONE, node);
  }
}

RewriteResponse max(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MAX);
  Assert(node.getNumChildren() == 2);

  FloatingPoint arg1(node[0].getConst<FloatingPoint>());
  FloatingPoint arg2(node[1].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  FloatingPoint::PartialFloatingPoint res(arg1.max(arg2));

  if (res.second)
  {
    Node lit = NodeManager::currentNM()->mkConst(res.first);
    return RewriteResponse(REWRITE_DONE, lit);
  }
  else
  {
    // Can't constant fold the underspecified case
    return RewriteResponse(REWRITE_DONE, node);
  }
}

RewriteResponse minTotal(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MIN_TOTAL);
  Assert(node.getNumChildren() == 3);

  FloatingPoint arg1(node[0].getConst<FloatingPoint>());
  FloatingPoint arg2(node[1].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  // Can be called with the third argument non-constant
  if (node[2].getMetaKind() == kind::metakind::CONSTANT)
  {
    BitVector arg3(node[2].getConst<BitVector>());

    FloatingPoint folded(arg1.minTotal(arg2, arg3.isBitSet(0)));
    Node lit = NodeManager::currentNM()->mkConst(folded);
    return RewriteResponse(REWRITE_DONE, lit);
  }
  else
  {
    FloatingPoint::PartialFloatingPoint res(arg1.min(arg2));

    if (res.second)
    {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    }
    else
    {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }
}

RewriteResponse maxTotal(TNode node, bool isPreRewrite)
{
  Assert(node.getKind() == kind::FLOATINGPOINT_MAX_TOTAL);
  Assert(node.getNumChildren() == 3);

  FloatingPoint arg1(node[0].getConst<FloatingPoint>());
  FloatingPoint arg2(node[1].getConst<FloatingPoint>());

  Assert(arg1.getSize() == arg2.getSize());

  // Can be called with the third argument non-constant
  if (node[2].getMetaKind() == kind::metakind::CONSTANT)
  {
    BitVector arg3(node[2].getConst<BitVector>());

    FloatingPoint folded(arg1.maxTotal(arg2, arg3.isBitSet(0)));
    Node lit = NodeManager::currentNM()->mkConst(folded);
    return RewriteResponse(REWRITE_DONE, lit);
  }
  else
  {
    FloatingPoint::PartialFloatingPoint res(arg1.max(arg2));

    if (res.second)
    {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    }
    else
    {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }
}

  RewriteResponse equal (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::EQUAL);

    // We should only get equalities of floating point or rounding mode types.
    TypeNode tn = node[0].getType(true);

    if (tn.isFloatingPoint()) {
      FloatingPoint arg1(node[0].getConst<FloatingPoint>());
      FloatingPoint arg2(node[1].getConst<FloatingPoint>());

      Assert(arg1.getSize() == arg2.getSize());

      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 == arg2));

    } else if (tn.isRoundingMode()) {
      RoundingMode arg1(node[0].getConst<RoundingMode>());
      RoundingMode arg2(node[1].getConst<RoundingMode>());
    
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 == arg2));

    }
    Unreachable() << "Equality of unknown type";
  }

  RewriteResponse leq(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_LEQ);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.getSize() == arg2.getSize());

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 <= arg2));
  }

  RewriteResponse lt(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_LT);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.getSize() == arg2.getSize());

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 < arg2));
  }

  RewriteResponse isNormal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_NORMAL);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNormal()));
  }

  RewriteResponse isSubnormal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_SUBNORMAL);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isSubnormal()));
  }

  RewriteResponse isZero(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_ZERO);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isZero()));
  }

  RewriteResponse isInfinite(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_INF);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isInfinite()));
  }

  RewriteResponse isNaN(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_NAN);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNaN()));
  }

  RewriteResponse isNegative(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_NEG);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNegative()));
  }

  RewriteResponse isPositive(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_IS_POS);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isPositive()));
  }

  RewriteResponse convertFromIEEEBitVectorLiteral(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV);

    TNode op = node.getOperator();
    const FloatingPointToFPIEEEBitVector &param = op.getConst<FloatingPointToFPIEEEBitVector>();
    const BitVector &bv = node[0].getConst<BitVector>();

    Node lit = NodeManager::currentNM()->mkConst(
        FloatingPoint(param.getSize().exponentWidth(),
                      param.getSize().significandWidth(),
                      bv));

    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse constantConvert(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_FP);
    Assert(node.getNumChildren() == 2);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPointToFPFloatingPoint info = node.getOperator().getConst<FloatingPointToFPFloatingPoint>();

    return RewriteResponse(
        REWRITE_DONE,
        NodeManager::currentNM()->mkConst(arg1.convert(info.getSize(), rm)));
  }

  RewriteResponse convertFromRealLiteral(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_REAL);

    TNode op = node.getOperator();
    const FloatingPointSize& size =
        op.getConst<FloatingPointToFPReal>().getSize();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    Rational arg(node[1].getConst<Rational>());

    FloatingPoint res(size, rm, arg);

    Node lit = NodeManager::currentNM()->mkConst(res);

    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse convertFromSBV(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_SBV);

    TNode op = node.getOperator();
    const FloatingPointSize& size =
        op.getConst<FloatingPointToFPSignedBitVector>().getSize();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    BitVector sbv(node[1].getConst<BitVector>());

    NodeManager* nm = NodeManager::currentNM();

    /* symFPU does not allow conversions from signed bit-vector of size 1 */
    if (sbv.getSize() == 1)
    {
      FloatingPoint fromubv(size, rm, sbv, false);
      if (sbv.isBitSet(0))
      {
        return RewriteResponse(REWRITE_DONE, nm->mkConst(fromubv.negate()));
      }
      return RewriteResponse(REWRITE_DONE, nm->mkConst(fromubv));
    }

    return RewriteResponse(REWRITE_DONE,
                           nm->mkConst(FloatingPoint(size, rm, sbv, true)));
  }

  RewriteResponse convertFromUBV(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FROM_UBV);

    TNode op = node.getOperator();
    const FloatingPointSize& size =
        op.getConst<FloatingPointToFPUnsignedBitVector>().getSize();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    BitVector arg(node[1].getConst<BitVector>());

    FloatingPoint res(size, rm, arg, false);

    Node lit = NodeManager::currentNM()->mkConst(res);

    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse convertToUBV(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV);

    TNode op = node.getOperator();
    const BitVectorSize& size = op.getConst<FloatingPointToUBV>().d_bv_size;

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    FloatingPoint::PartialBitVector res(arg.convertToBV(size, rm, false));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToSBV(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV);

    TNode op = node.getOperator();
    const BitVectorSize& size = op.getConst<FloatingPointToSBV>().d_bv_size;

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    FloatingPoint::PartialBitVector res(arg.convertToBV(size, rm, true));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToReal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL);

    FloatingPoint arg(node[0].getConst<FloatingPoint>());

    FloatingPoint::PartialRational res(arg.convertToRational());

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConstReal(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToUBVTotal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV_TOTAL);

    TNode op = node.getOperator();
    const BitVectorSize& size =
        op.getConst<FloatingPointToUBVTotal>().d_bv_size;

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector partialValue(node[2].getConst<BitVector>());

      BitVector folded(arg.convertToBVTotal(size, rm, false, partialValue));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialBitVector res(arg.convertToBV(size, rm, false));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse convertToSBVTotal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV_TOTAL);

    TNode op = node.getOperator();
    const BitVectorSize& size =
        op.getConst<FloatingPointToSBVTotal>().d_bv_size;

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector partialValue(node[2].getConst<BitVector>());

      BitVector folded(arg.convertToBVTotal(size, rm, true, partialValue));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialBitVector res(arg.convertToBV(size, rm, true));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse convertToRealTotal(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL);

    FloatingPoint arg(node[0].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[1].getMetaKind() == kind::metakind::CONSTANT) {
      Rational partialValue(node[1].getConst<Rational>());

      Rational folded(arg.convertToRationalTotal(partialValue));
      Node lit = NodeManager::currentNM()->mkConstReal(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialRational res(arg.convertToRational());

      if (res.second) {
        Node lit = NodeManager::currentNM()->mkConstReal(res.first);
        return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse componentFlag(TNode node, bool isPreRewrite)
  {
    Kind k = node.getKind();

    Assert((k == kind::FLOATINGPOINT_COMPONENT_NAN)
           || (k == kind::FLOATINGPOINT_COMPONENT_INF)
           || (k == kind::FLOATINGPOINT_COMPONENT_ZERO)
           || (k == kind::FLOATINGPOINT_COMPONENT_SIGN));

    FloatingPoint arg0(node[0].getConst<FloatingPoint>());

    bool result;
    switch (k)
    {
      case kind::FLOATINGPOINT_COMPONENT_NAN: result = arg0.isNaN(); break;
      case kind::FLOATINGPOINT_COMPONENT_INF: result = arg0.isInfinite(); break;
      case kind::FLOATINGPOINT_COMPONENT_ZERO: result = arg0.isZero(); break;
      case kind::FLOATINGPOINT_COMPONENT_SIGN: result = arg0.getSign(); break;
      default: Unreachable() << "Unknown kind used in componentFlag"; break;
    }

    BitVector res(1U, (result) ? 1U : 0U);

    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(res));
  }

  RewriteResponse componentExponent(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_COMPONENT_EXPONENT);

    FloatingPoint arg0(node[0].getConst<FloatingPoint>());

    // \todo Add a proper interface for this sort of thing to FloatingPoint #1915
    return RewriteResponse(
        REWRITE_DONE,
        NodeManager::currentNM()->mkConst((BitVector)arg0.getExponent())
    );
  }

  RewriteResponse componentSignificand(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);

    FloatingPoint arg0(node[0].getConst<FloatingPoint>());

    return RewriteResponse(
        REWRITE_DONE,
        NodeManager::currentNM()->mkConst((BitVector)arg0.getSignificand())
    );
  }

  RewriteResponse roundingModeBitBlast(TNode node, bool isPreRewrite)
  {
    Assert(node.getKind() == kind::ROUNDINGMODE_BITBLAST);

    BitVector value;

    /* \todo fix the numbering of rounding modes so this doesn't need
     * to call symfpu at all and remove the dependency on fp_converter.h #1915 */
    RoundingMode arg0(node[0].getConst<RoundingMode>());
    switch (arg0)
    {
      case RoundingMode::ROUND_NEAREST_TIES_TO_EVEN:
        value = symfpuSymbolic::traits::RNE().getConst<BitVector>();
        break;

      case RoundingMode::ROUND_NEAREST_TIES_TO_AWAY:
        value = symfpuSymbolic::traits::RNA().getConst<BitVector>();
        break;

      case RoundingMode::ROUND_TOWARD_POSITIVE:
        value = symfpuSymbolic::traits::RTP().getConst<BitVector>();
        break;

      case RoundingMode::ROUND_TOWARD_NEGATIVE:
        value = symfpuSymbolic::traits::RTN().getConst<BitVector>();
        break;

      case RoundingMode::ROUND_TOWARD_ZERO:
        value = symfpuSymbolic::traits::RTZ().getConst<BitVector>();
        break;

      default:
        Unreachable() << "Unknown rounding mode in roundingModeBitBlast";
        break;
    }
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(value));
  }

  };  // namespace constantFold

  /**
   * Initialize the rewriter.
   */
  TheoryFpRewriter::TheoryFpRewriter(context::UserContext* u) : d_fpExpDef(u)
  {
    /* Set up the pre-rewrite dispatch table */
    for (uint32_t i = 0; i < kind::LAST_KIND; ++i)
    {
      d_preRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    d_preRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    d_preRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity;

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    // d_preRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    d_preRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;

    /******** Operations ********/
    d_preRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::compactAbs;
    d_preRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    d_preRewriteTable[kind::FLOATINGPOINT_ADD] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_SUB] =
        rewrite::convertSubtractionToAddition;
    d_preRewriteTable[kind::FLOATINGPOINT_MULT] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::compactMinMax;
    d_preRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::compactMinMax;
    d_preRewriteTable[kind::FLOATINGPOINT_MIN_TOTAL] = rewrite::compactMinMax;
    d_preRewriteTable[kind::FLOATINGPOINT_MAX_TOTAL] = rewrite::compactMinMax;

    /******** Comparisons ********/
    d_preRewriteTable[kind::FLOATINGPOINT_EQ] =
        rewrite::then<rewrite::breakChain, rewrite::ieeeEqToEq>;
    d_preRewriteTable[kind::FLOATINGPOINT_LEQ] =
        rewrite::then<rewrite::breakChain, rewrite::leqId>;
    d_preRewriteTable[kind::FLOATINGPOINT_LT] =
        rewrite::then<rewrite::breakChain, rewrite::ltId>;
    d_preRewriteTable[kind::FLOATINGPOINT_GEQ] =
        rewrite::then<rewrite::breakChain, rewrite::geqToleq>;
    d_preRewriteTable[kind::FLOATINGPOINT_GT] =
        rewrite::then<rewrite::breakChain, rewrite::gtTolt>;

    /******** Classifications ********/
    d_preRewriteTable[kind::FLOATINGPOINT_IS_NORMAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_SUBNORMAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_ZERO] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_INF] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_NAN] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_NEG] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_IS_POS] = rewrite::identity;

    /******** Conversions ********/
    d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV] =
        rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_FP] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_REAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_SBV] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_UBV] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] = rewrite::identity;

    /******** Variables ********/
    d_preRewriteTable[kind::VARIABLE] = rewrite::variable;
    d_preRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;
    d_preRewriteTable[kind::SKOLEM] = rewrite::variable;
    d_preRewriteTable[kind::INST_CONSTANT] = rewrite::variable;

    d_preRewriteTable[kind::EQUAL] = rewrite::equal;

    /******** Components for bit-blasting ********/
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_NAN] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_INF] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_ZERO] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_SIGN] = rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_EXPONENT] =
        rewrite::identity;
    d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND] =
        rewrite::identity;
    d_preRewriteTable[kind::ROUNDINGMODE_BITBLAST] = rewrite::identity;

    /* Set up the post-rewrite dispatch table */
    for (uint32_t i = 0; i < kind::LAST_KIND; ++i)
    {
      d_postRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    d_postRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    d_postRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity;

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    // d_postRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    d_postRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;

    /******** Operations ********/
    d_postRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::compactAbs;
    d_postRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    d_postRewriteTable[kind::FLOATINGPOINT_ADD] =
        rewrite::reorderBinaryOperation;
    d_postRewriteTable[kind::FLOATINGPOINT_SUB] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_MULT] =
        rewrite::reorderBinaryOperation;
    d_postRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::reorderFMA;
    d_postRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::compactRemainder;
    d_postRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::compactMinMax;
    d_postRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::compactMinMax;
    d_postRewriteTable[kind::FLOATINGPOINT_MIN_TOTAL] = rewrite::compactMinMax;
    d_postRewriteTable[kind::FLOATINGPOINT_MAX_TOTAL] = rewrite::compactMinMax;

    /******** Comparisons ********/
    d_postRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::leqId;
    d_postRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::ltId;
    d_postRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::identity;

    /******** Classifications ********/
    d_postRewriteTable[kind::FLOATINGPOINT_IS_NORMAL] =
        rewrite::removeSignOperations;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_SUBNORMAL] =
        rewrite::removeSignOperations;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_ZERO] =
        rewrite::removeSignOperations;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_INF] =
        rewrite::removeSignOperations;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_NAN] =
        rewrite::removeSignOperations;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_NEG] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_IS_POS] = rewrite::identity;

    /******** Conversions ********/
    d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV] =
        rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_FP] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_REAL] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_SBV] =
        rewrite::toFPSignedBV;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FROM_UBV] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] = rewrite::identity;

    /******** Variables ********/
    d_postRewriteTable[kind::VARIABLE] = rewrite::variable;
    d_postRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;
    d_postRewriteTable[kind::SKOLEM] = rewrite::variable;
    d_postRewriteTable[kind::INST_CONSTANT] = rewrite::variable;

    d_postRewriteTable[kind::EQUAL] = rewrite::equal;

    /******** Components for bit-blasting ********/
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_NAN] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_INF] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_ZERO] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_SIGN] = rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_EXPONENT] =
        rewrite::identity;
    d_postRewriteTable[kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND] =
        rewrite::identity;
    d_postRewriteTable[kind::ROUNDINGMODE_BITBLAST] = rewrite::identity;

    /* Set up the post-rewrite constant fold table */
    for (uint32_t i = 0; i < kind::LAST_KIND; ++i)
    {
      // Note that this is identity, not notFP
      // Constant folding is called after post-rewrite
      // So may have to deal with cases of things being
      // re-written to non-floating-point sorts (i.e. true).
      d_constantFoldTable[i] = rewrite::identity;
    }

    /******** Constants ********/
    /* Already folded! */
    d_constantFoldTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    d_constantFoldTable[kind::CONST_ROUNDINGMODE] = rewrite::identity;

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    d_constantFoldTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;

    /******** Operations ********/
    d_constantFoldTable[kind::FLOATINGPOINT_FP] = constantFold::fpLiteral;
    d_constantFoldTable[kind::FLOATINGPOINT_ABS] = constantFold::abs;
    d_constantFoldTable[kind::FLOATINGPOINT_NEG] = constantFold::neg;
    d_constantFoldTable[kind::FLOATINGPOINT_ADD] = constantFold::add;
    d_constantFoldTable[kind::FLOATINGPOINT_MULT] = constantFold::mult;
    d_constantFoldTable[kind::FLOATINGPOINT_DIV] = constantFold::div;
    d_constantFoldTable[kind::FLOATINGPOINT_FMA] = constantFold::fma;
    d_constantFoldTable[kind::FLOATINGPOINT_SQRT] = constantFold::sqrt;
    d_constantFoldTable[kind::FLOATINGPOINT_REM] = constantFold::rem;
    d_constantFoldTable[kind::FLOATINGPOINT_RTI] = constantFold::rti;
    d_constantFoldTable[kind::FLOATINGPOINT_MIN] = constantFold::min;
    d_constantFoldTable[kind::FLOATINGPOINT_MAX] = constantFold::max;
    d_constantFoldTable[kind::FLOATINGPOINT_MIN_TOTAL] = constantFold::minTotal;
    d_constantFoldTable[kind::FLOATINGPOINT_MAX_TOTAL] = constantFold::maxTotal;

    /******** Comparisons ********/
    d_constantFoldTable[kind::FLOATINGPOINT_LEQ] = constantFold::leq;
    d_constantFoldTable[kind::FLOATINGPOINT_LT] = constantFold::lt;

    /******** Classifications ********/
    d_constantFoldTable[kind::FLOATINGPOINT_IS_NORMAL] = constantFold::isNormal;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_SUBNORMAL] =
        constantFold::isSubnormal;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_ZERO] = constantFold::isZero;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_INF] = constantFold::isInfinite;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_NAN] = constantFold::isNaN;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_NEG] = constantFold::isNegative;
    d_constantFoldTable[kind::FLOATINGPOINT_IS_POS] = constantFold::isPositive;

    /******** Conversions ********/
    d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FROM_IEEE_BV] =
        constantFold::convertFromIEEEBitVectorLiteral;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FROM_FP] =
        constantFold::constantConvert;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FROM_REAL] =
        constantFold::convertFromRealLiteral;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FROM_SBV] =
        constantFold::convertFromSBV;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FROM_UBV] =
        constantFold::convertFromUBV;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_UBV] =
        constantFold::convertToUBV;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_SBV] =
        constantFold::convertToSBV;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_REAL] =
        constantFold::convertToReal;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] =
        constantFold::convertToUBVTotal;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] =
        constantFold::convertToSBVTotal;
    d_constantFoldTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] =
        constantFold::convertToRealTotal;

    /******** Variables ********/
    d_constantFoldTable[kind::VARIABLE] = rewrite::variable;
    d_constantFoldTable[kind::BOUND_VARIABLE] = rewrite::variable;

    d_constantFoldTable[kind::EQUAL] = constantFold::equal;

    /******** Components for bit-blasting ********/
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_NAN] =
        constantFold::componentFlag;
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_INF] =
        constantFold::componentFlag;
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_ZERO] =
        constantFold::componentFlag;
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_SIGN] =
        constantFold::componentFlag;
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_EXPONENT] =
        constantFold::componentExponent;
    d_constantFoldTable[kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND] =
        constantFold::componentSignificand;
    d_constantFoldTable[kind::ROUNDINGMODE_BITBLAST] =
        constantFold::roundingModeBitBlast;
}

  /**
   * Rewrite a node into the normal form for the theory of fp
   * in pre-order (really topological order)---meaning that the
   * children may not be in the normal form.  This is an optimization
   * for theories with cancelling terms (e.g., 0 * (big-nasty-expression)
   * in arithmetic rewrites to 0 without the need to look at the big
   * nasty expression).  Since it's only an optimization, the
   * implementation here can do nothing.
   */

  RewriteResponse TheoryFpRewriter::preRewrite(TNode node) {
    Trace("fp-rewrite") << "TheoryFpRewriter::preRewrite(): " << node << std::endl;
    RewriteResponse res = d_preRewriteTable[node.getKind()](node, true);
    if (res.d_node != node)
    {
      Trace("fp-rewrite") << "TheoryFpRewriter::preRewrite(): before " << node << std::endl;
      Trace("fp-rewrite") << "TheoryFpRewriter::preRewrite(): after  "
                          << res.d_node << std::endl;
    }
    return res;
  }


  /**
   * Rewrite a node into the normal form for the theory of fp.
   * Called in post-order (really reverse-topological order) when
   * traversing the expression DAG during rewriting.  This is the
   * main function of the rewriter, and because of the ordering,
   * it can assume its children are all rewritten already.
   *
   * This function can return one of three rewrite response codes
   * along with the rewritten node:
   *
   *   REWRITE_DONE indicates that no more rewriting is needed.
   *   REWRITE_AGAIN means that the top-level expression should be
   *     rewritten again, but that its children are in final form.
   *   REWRITE_AGAIN_FULL means that the entire returned expression
   *     should be rewritten again (top-down with preRewrite(), then
   *     bottom-up with postRewrite()).
   *
   * Even if this function returns REWRITE_DONE, if the returned
   * expression belongs to a different theory, it will be fully
   * rewritten by that theory's rewriter.
   */

  RewriteResponse TheoryFpRewriter::postRewrite(TNode node) {
    Trace("fp-rewrite") << "TheoryFpRewriter::postRewrite(): " << node << std::endl;
    RewriteResponse res = d_postRewriteTable[node.getKind()](node, false);
    if (res.d_node != node)
    {
      Trace("fp-rewrite") << "TheoryFpRewriter::postRewrite(): before " << node << std::endl;
      Trace("fp-rewrite") << "TheoryFpRewriter::postRewrite(): after  "
                          << res.d_node << std::endl;
    }

    if (res.d_status == REWRITE_DONE)
    {
      bool allChildrenConst = true;
      bool apartFromRoundingMode = false;
      bool apartFromPartiallyDefinedArgument = false;
      for (Node::const_iterator i = res.d_node.begin(); i != res.d_node.end();
           ++i)
      {
        if ((*i).getMetaKind() != kind::metakind::CONSTANT) {
	  if ((*i).getType().isRoundingMode() && !apartFromRoundingMode) {
	    apartFromRoundingMode = true;
          }
          else if ((res.d_node.getKind() == kind::FLOATINGPOINT_MIN_TOTAL
                    || res.d_node.getKind() == kind::FLOATINGPOINT_MAX_TOTAL
                    || res.d_node.getKind() == kind::FLOATINGPOINT_TO_UBV_TOTAL
                    || res.d_node.getKind() == kind::FLOATINGPOINT_TO_SBV_TOTAL
                    || res.d_node.getKind()
                           == kind::FLOATINGPOINT_TO_REAL_TOTAL)
                   && ((*i).getType().isBitVector() || (*i).getType().isReal())
                   && !apartFromPartiallyDefinedArgument)
          {
            apartFromPartiallyDefinedArgument = true;
          }
          else
          {
            allChildrenConst = false;
	    break;
          }
        }
      }

      if (allChildrenConst)
      {
        RewriteStatus rs = REWRITE_DONE;  // This is a bit messy because
        Node rn = res.d_node;             // RewriteResponse is too functional..

        if (apartFromRoundingMode)
        {
          if (!(res.d_node.getKind() == kind::EQUAL)
              &&  // Avoid infinite recursion...
              !(res.d_node.getKind() == kind::ROUNDINGMODE_BITBLAST))
          {
            // Don't eliminate the bit-blast
            // We are close to being able to constant fold this
            // and in many cases the rounding mode really doesn't matter.
            // So we can try brute forcing our way through them.

            NodeManager* nm = NodeManager::currentNM();

            Node rne(nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_EVEN));
            Node rna(nm->mkConst(RoundingMode::ROUND_NEAREST_TIES_TO_AWAY));
            Node rtz(nm->mkConst(RoundingMode::ROUND_TOWARD_POSITIVE));
            Node rtn(nm->mkConst(RoundingMode::ROUND_TOWARD_NEGATIVE));
            Node rtp(nm->mkConst(RoundingMode::ROUND_TOWARD_ZERO));

            TNode rm(res.d_node[0]);

            Node w_rne(res.d_node.substitute(rm, TNode(rne)));
            Node w_rna(res.d_node.substitute(rm, TNode(rna)));
            Node w_rtz(res.d_node.substitute(rm, TNode(rtz)));
            Node w_rtn(res.d_node.substitute(rm, TNode(rtn)));
            Node w_rtp(res.d_node.substitute(rm, TNode(rtp)));

            rs = REWRITE_AGAIN_FULL;
            rn = nm->mkNode(
                kind::ITE,
                nm->mkNode(kind::EQUAL, rm, rne),
                w_rne,
                nm->mkNode(
                    kind::ITE,
                    nm->mkNode(kind::EQUAL, rm, rna),
                    w_rna,
                    nm->mkNode(kind::ITE,
                               nm->mkNode(kind::EQUAL, rm, rtz),
                               w_rtz,
                               nm->mkNode(kind::ITE,
                                          nm->mkNode(kind::EQUAL, rm, rtn),
                                          w_rtn,
                                          w_rtp))));
          }
        }
        else
        {
          RewriteResponse tmp =
              d_constantFoldTable[res.d_node.getKind()](res.d_node, false);
          rs = tmp.d_status;
          rn = tmp.d_node;
        }

        RewriteResponse constRes(rs, rn);

        if (constRes.d_node != res.d_node)
        {
          Trace("fp-rewrite")
              << "TheoryFpRewriter::postRewrite(): before constant fold "
              << res.d_node << std::endl;
          Trace("fp-rewrite")
              << "TheoryFpRewriter::postRewrite(): after constant fold "
              << constRes.d_node << std::endl;
        }

        return constRes;
      }
    }

    return res;
  }
  TrustNode TheoryFpRewriter::expandDefinition(Node node)
  {
    return d_fpExpDef.expandDefinition(node);
  }

  }  // namespace fp
  }  // namespace theory
  }  // namespace cvc5::internal

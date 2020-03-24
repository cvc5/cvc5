/*********************                                                        */
/*! \file theory_fp_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Martin Brain, Andrew Reynolds
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Rewrite rules for floating point theories. ]]
 **
 ** \todo [[ Single argument constant propagate / simplify
             Push negations through arithmetic operators (include max and min? maybe not due to +0/-0)
 **          classifications to normal tests (maybe)
 **          (= x (fp.neg x)) --> (isNaN x)
 **          (fp.eq x (fp.neg x)) --> (isZero x)   (previous and reorganise should be sufficient)
 **          (fp.eq x const) --> various = depending on const
 **          (fp.isPositive (fp.neg x)) --> (fp.isNegative x)
 **          (fp.isNegative (fp.neg x)) --> (fp.isPositive x)
 **          (fp.isPositive (fp.abs x)) --> (not (isNaN x))
 **          (fp.isNegative (fp.abs x)) --> false
 **          A -> castA --> A
 **          A -> castB -> castC  -->  A -> castC if A <= B <= C
 **          A -> castB -> castA  -->  A if A <= B
 **          promotion converts can ignore rounding mode
 **          Samuel Figuer results
 **       ]]
 **/

#include <algorithm>

#include "base/check.h"
#include "theory/fp/fp_converter.h"
#include "theory/fp/theory_fp_rewriter.h"

namespace CVC4 {
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

  RewriteResponse notFP (TNode node, bool) {
    Unreachable() << "non floating-point kind (" << node.getKind()
                  << ") in floating point rewrite?";
  }

  RewriteResponse identity (TNode node, bool) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse type (TNode node, bool) {
    Unreachable() << "sort kind (" << node.getKind()
                  << ") found in expression?";
  }

  RewriteResponse removeDoubleNegation (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
    if (node[0].getKind() == kind::FLOATINGPOINT_NEG) {
      return RewriteResponse(REWRITE_AGAIN, node[0][0]);
    }

    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse compactAbs (TNode node, bool) {
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

  RewriteResponse convertSubtractionToAddition (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_SUB);
    Node negation = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_NEG,node[2]);
    Node addition = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_PLUS,node[0],node[1],negation);
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

      NodeBuilder<> conjunction(kind::AND);

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

  RewriteResponse ieeeEqToEq (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_EQ);
    NodeManager *nm = NodeManager::currentNM();

    return RewriteResponse(REWRITE_DONE,
			   nm->mkNode(kind::AND,
				      nm->mkNode(kind::AND,
						 nm->mkNode(kind::NOT, nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[0])),
						 nm->mkNode(kind::NOT, nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[1]))),
				      nm->mkNode(kind::OR,
						 nm->mkNode(kind::EQUAL, node[0], node[1]),
						 nm->mkNode(kind::AND,
							    nm->mkNode(kind::FLOATINGPOINT_ISZ, node[0]),
							    nm->mkNode(kind::FLOATINGPOINT_ISZ, node[1])))));
  }


  RewriteResponse geqToleq (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_GEQ);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LEQ,node[1],node[0]));
  }

  RewriteResponse gtTolt (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_GT);
    return RewriteResponse(REWRITE_DONE,NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_LT,node[1],node[0]));
  }

  RewriteResponse removed(TNode node, bool)
  {
    Unreachable() << "kind (" << node.getKind()
                  << ") should have been removed?";
  }

  RewriteResponse variable (TNode node, bool) {  
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
#ifdef CVC4_ASSERTIONS
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
    Assert((k == kind::FLOATINGPOINT_PLUS) || (k == kind::FLOATINGPOINT_MULT));
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
      Node normal = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_FMA,node[0],node[2],node[1],node[3]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse removeSignOperations (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISN
           || node.getKind() == kind::FLOATINGPOINT_ISSN
           || node.getKind() == kind::FLOATINGPOINT_ISZ
           || node.getKind() == kind::FLOATINGPOINT_ISINF
           || node.getKind() == kind::FLOATINGPOINT_ISNAN);
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
                     nm->mkNode(kind::FLOATINGPOINT_ISNAN, node[0])));
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

}; /* CVC4::theory::fp::rewrite */


namespace constantFold {


  RewriteResponse fpLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_FP);

    BitVector bv(node[0].getConst<BitVector>());
    bv = bv.concat(node[1].getConst<BitVector>());
    bv = bv.concat(node[2].getConst<BitVector>());
    
    // +1 to support the hidden bit
    Node lit =
      NodeManager::currentNM()->mkConst(FloatingPoint(node[1].getConst<BitVector>().getSize(),
						      node[2].getConst<BitVector>().getSize() + 1,
						      bv));
    
    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse abs (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ABS);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().absolute()));
  }


  RewriteResponse neg (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().negate()));
  }


  RewriteResponse plus (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_PLUS);
    Assert(node.getNumChildren() == 3);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPoint arg2(node[2].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.plus(rm, arg2)));
  }

  RewriteResponse mult (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_MULT);
    Assert(node.getNumChildren() == 3);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPoint arg2(node[2].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.mult(rm, arg2)));
  }

  RewriteResponse fma (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_FMA);
    Assert(node.getNumChildren() == 4);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPoint arg2(node[2].getConst<FloatingPoint>());
    FloatingPoint arg3(node[3].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);
    Assert(arg1.t == arg3.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.fma(rm, arg2, arg3)));
  }

  RewriteResponse div (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_DIV);
    Assert(node.getNumChildren() == 3);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPoint arg2(node[2].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.div(rm, arg2)));
  }
  
  RewriteResponse sqrt (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_SQRT);
    Assert(node.getNumChildren() == 2);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());
    
    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg.sqrt(rm)));
  }

  RewriteResponse rti (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_RTI);
    Assert(node.getNumChildren() == 2);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());
    
    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg.rti(rm)));
  }

  RewriteResponse rem (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_REM);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.rem(arg2)));
  }

  RewriteResponse min (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_MIN);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    FloatingPoint::PartialFloatingPoint res(arg1.min(arg2));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse max (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_MAX);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    FloatingPoint::PartialFloatingPoint res(arg1.max(arg2));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse minTotal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_MIN_TOTAL);
    Assert(node.getNumChildren() == 3);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector arg3(node[2].getConst<BitVector>());

      FloatingPoint folded(arg1.minTotal(arg2, arg3.isBitSet(0)));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialFloatingPoint res(arg1.min(arg2));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse maxTotal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_MAX_TOTAL);
    Assert(node.getNumChildren() == 3);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector arg3(node[2].getConst<BitVector>());

      FloatingPoint folded(arg1.maxTotal(arg2, arg3.isBitSet(0)));
      Node lit = NodeManager::currentNM()->mkConst(folded);
     return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialFloatingPoint res(arg1.max(arg2));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
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

      Assert(arg1.t == arg2.t);

      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 == arg2));

    } else if (tn.isRoundingMode()) {
      RoundingMode arg1(node[0].getConst<RoundingMode>());
      RoundingMode arg2(node[1].getConst<RoundingMode>());
    
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 == arg2));

    }
    Unreachable() << "Equality of unknown type";
  }


  RewriteResponse leq (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_LEQ);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 <= arg2));
  }


  RewriteResponse lt (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_LT);
    Assert(node.getNumChildren() == 2);

    FloatingPoint arg1(node[0].getConst<FloatingPoint>());
    FloatingPoint arg2(node[1].getConst<FloatingPoint>());

    Assert(arg1.t == arg2.t);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1 < arg2));
  }


  RewriteResponse isNormal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISN);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNormal()));
  }

  RewriteResponse isSubnormal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISSN);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isSubnormal()));
  }

  RewriteResponse isZero (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISZ);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isZero()));
  }

  RewriteResponse isInfinite (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISINF);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isInfinite()));
  }

  RewriteResponse isNaN (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISNAN);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNaN()));
  }

  RewriteResponse isNegative (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISNEG);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isNegative()));
  }

  RewriteResponse isPositive (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISPOS);
    Assert(node.getNumChildren() == 1);

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(node[0].getConst<FloatingPoint>().isPositive()));
  }

  RewriteResponse convertFromIEEEBitVectorLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);

    TNode op = node.getOperator();
    const FloatingPointToFPIEEEBitVector &param = op.getConst<FloatingPointToFPIEEEBitVector>();
    const BitVector &bv = node[0].getConst<BitVector>();
    
    Node lit =
      NodeManager::currentNM()->mkConst(FloatingPoint(param.t.exponent(),
						      param.t.significand(),
						      bv));
    
    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse constantConvert (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT);
    Assert(node.getNumChildren() == 2);

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg1(node[1].getConst<FloatingPoint>());
    FloatingPointToFPFloatingPoint info = node.getOperator().getConst<FloatingPointToFPFloatingPoint>();

    return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(arg1.convert(info.t,rm)));
  }

  RewriteResponse convertFromRealLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);

    TNode op = node.getOperator();
    const FloatingPointToFPReal &param = op.getConst<FloatingPointToFPReal>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    Rational arg(node[1].getConst<Rational>());

    FloatingPoint res(param.t, rm, arg);
    
    Node lit = NodeManager::currentNM()->mkConst(res);
    
    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse convertFromSBV (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR);

    TNode op = node.getOperator();
    const FloatingPointToFPSignedBitVector &param = op.getConst<FloatingPointToFPSignedBitVector>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    BitVector arg(node[1].getConst<BitVector>());

    FloatingPoint res(param.t, rm, arg, true);
    
    Node lit = NodeManager::currentNM()->mkConst(res);
    
    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse convertFromUBV (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR);

    TNode op = node.getOperator();
    const FloatingPointToFPUnsignedBitVector &param = op.getConst<FloatingPointToFPUnsignedBitVector>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    BitVector arg(node[1].getConst<BitVector>());

    FloatingPoint res(param.t, rm, arg, false);
    
    Node lit = NodeManager::currentNM()->mkConst(res);
    
    return RewriteResponse(REWRITE_DONE, lit);
  }

  RewriteResponse convertToUBV (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV);

    TNode op = node.getOperator();
    const FloatingPointToUBV &param = op.getConst<FloatingPointToUBV>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    FloatingPoint::PartialBitVector res(arg.convertToBV(param.bvs, rm, false));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToSBV (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV);

    TNode op = node.getOperator();
    const FloatingPointToSBV &param = op.getConst<FloatingPointToSBV>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    FloatingPoint::PartialBitVector res(arg.convertToBV(param.bvs, rm, true));

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToReal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL);

    FloatingPoint arg(node[0].getConst<FloatingPoint>());

    FloatingPoint::PartialRational res(arg.convertToRational());

    if (res.second) {
      Node lit = NodeManager::currentNM()->mkConst(res.first);
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      // Can't constant fold the underspecified case
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertToUBVTotal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_UBV_TOTAL);

    TNode op = node.getOperator();
    const FloatingPointToUBVTotal &param = op.getConst<FloatingPointToUBVTotal>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector partialValue(node[2].getConst<BitVector>());

      BitVector folded(arg.convertToBVTotal(param.bvs, rm, false, partialValue));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialBitVector res(arg.convertToBV(param.bvs, rm, false));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse convertToSBVTotal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_SBV_TOTAL);

    TNode op = node.getOperator();
    const FloatingPointToSBVTotal &param = op.getConst<FloatingPointToSBVTotal>();

    RoundingMode rm(node[0].getConst<RoundingMode>());
    FloatingPoint arg(node[1].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[2].getMetaKind() == kind::metakind::CONSTANT) {
      BitVector partialValue(node[2].getConst<BitVector>());

      BitVector folded(arg.convertToBVTotal(param.bvs, rm, true, partialValue));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {

      FloatingPoint::PartialBitVector res(arg.convertToBV(param.bvs, rm, true));

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse convertToRealTotal (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL);

    FloatingPoint arg(node[0].getConst<FloatingPoint>());

    // Can be called with the third argument non-constant
    if (node[1].getMetaKind() == kind::metakind::CONSTANT) {
      Rational partialValue(node[1].getConst<Rational>());

      Rational folded(arg.convertToRationalTotal(partialValue));
      Node lit = NodeManager::currentNM()->mkConst(folded);
      return RewriteResponse(REWRITE_DONE, lit);

    } else {
      FloatingPoint::PartialRational res(arg.convertToRational());

      if (res.second) {
	Node lit = NodeManager::currentNM()->mkConst(res.first);
	return RewriteResponse(REWRITE_DONE, lit);
      } else {
	// Can't constant fold the underspecified case
	return RewriteResponse(REWRITE_DONE, node);
      }
    }
  }

  RewriteResponse componentFlag(TNode node, bool)
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
#ifdef CVC4_USE_SYMFPU
      case kind::FLOATINGPOINT_COMPONENT_NAN:
        result = arg0.getLiteral().nan;
        break;
      case kind::FLOATINGPOINT_COMPONENT_INF:
        result = arg0.getLiteral().inf;
        break;
      case kind::FLOATINGPOINT_COMPONENT_ZERO:
        result = arg0.getLiteral().zero;
        break;
      case kind::FLOATINGPOINT_COMPONENT_SIGN:
        result = arg0.getLiteral().sign;
        break;
#endif
      default: Unreachable() << "Unknown kind used in componentFlag"; break;
    }

    BitVector res(1U, (result) ? 1U : 0U);

    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(res));
  }

  RewriteResponse componentExponent(TNode node, bool)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_COMPONENT_EXPONENT);

    FloatingPoint arg0(node[0].getConst<FloatingPoint>());

    // \todo Add a proper interface for this sort of thing to FloatingPoint #1915
    return RewriteResponse(
        REWRITE_DONE,
#ifdef CVC4_USE_SYMFPU
        NodeManager::currentNM()->mkConst((BitVector)arg0.getLiteral().exponent)
#else
        node
#endif
            );
  }

  RewriteResponse componentSignificand(TNode node, bool)
  {
    Assert(node.getKind() == kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND);

    FloatingPoint arg0(node[0].getConst<FloatingPoint>());

    return RewriteResponse(REWRITE_DONE,
#ifdef CVC4_USE_SYMFPU
                           NodeManager::currentNM()->mkConst(
                               (BitVector)arg0.getLiteral().significand)
#else
                           node
#endif
                               );
  }

  RewriteResponse roundingModeBitBlast(TNode node, bool)
  {
    Assert(node.getKind() == kind::ROUNDINGMODE_BITBLAST);

    BitVector value;

#ifdef CVC4_USE_SYMFPU
    /* \todo fix the numbering of rounding modes so this doesn't need
     * to call symfpu at all and remove the dependency on fp_converter.h #1915 */
    RoundingMode arg0(node[0].getConst<RoundingMode>());
    switch (arg0)
    {
      case roundNearestTiesToEven:
        value = symfpuSymbolic::traits::RNE().getConst<BitVector>();
        break;

      case roundNearestTiesToAway:
        value = symfpuSymbolic::traits::RNA().getConst<BitVector>();
        break;

      case roundTowardPositive:
        value = symfpuSymbolic::traits::RTP().getConst<BitVector>();
        break;

      case roundTowardNegative:
        value = symfpuSymbolic::traits::RTN().getConst<BitVector>();
        break;

      case roundTowardZero:
        value = symfpuSymbolic::traits::RTZ().getConst<BitVector>();
        break;

      default:
        Unreachable() << "Unknown rounding mode in roundingModeBitBlast";
        break;
    }
#else
    value = BitVector(5U, 0U);
#endif
    return RewriteResponse(REWRITE_DONE,
                           NodeManager::currentNM()->mkConst(value));
  }

};  /* CVC4::theory::fp::constantFold */


  /**
   * Initialize the rewriter.
   */
TheoryFpRewriter::TheoryFpRewriter()
{
  /* Set up the pre-rewrite dispatch table */
  for (unsigned i = 0; i < kind::LAST_KIND; ++i)
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
  d_preRewriteTable[kind::FLOATINGPOINT_PLUS] = rewrite::identity;
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
  d_preRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISNEG] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_ISPOS] = rewrite::identity;

  /******** Conversions ********/
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] =
      rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] =
      rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] =
      rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] =
      rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::identity;
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
  d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_EXPONENT] = rewrite::identity;
  d_preRewriteTable[kind::FLOATINGPOINT_COMPONENT_SIGNIFICAND] =
      rewrite::identity;
  d_preRewriteTable[kind::ROUNDINGMODE_BITBLAST] = rewrite::identity;

  /* Set up the post-rewrite dispatch table */
  for (unsigned i = 0; i < kind::LAST_KIND; ++i)
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
  d_postRewriteTable[kind::FLOATINGPOINT_PLUS] =
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
  d_postRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::removeSignOperations;
  d_postRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::removeSignOperations;
  d_postRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::removeSignOperations;
  d_postRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::removeSignOperations;
  d_postRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::removeSignOperations;
  d_postRewriteTable[kind::FLOATINGPOINT_ISNEG] = rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_ISPOS] = rewrite::identity;

  /******** Conversions ********/
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] =
      rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] =
      rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] =
      rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] =
      rewrite::identity;
  d_postRewriteTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::identity;
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
  for (unsigned i = 0; i < kind::LAST_KIND; ++i)
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
  d_constantFoldTable[kind::FLOATINGPOINT_PLUS] = constantFold::plus;
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
  d_constantFoldTable[kind::FLOATINGPOINT_ISN] = constantFold::isNormal;
  d_constantFoldTable[kind::FLOATINGPOINT_ISSN] = constantFold::isSubnormal;
  d_constantFoldTable[kind::FLOATINGPOINT_ISZ] = constantFold::isZero;
  d_constantFoldTable[kind::FLOATINGPOINT_ISINF] = constantFold::isInfinite;
  d_constantFoldTable[kind::FLOATINGPOINT_ISNAN] = constantFold::isNaN;
  d_constantFoldTable[kind::FLOATINGPOINT_ISNEG] = constantFold::isNegative;
  d_constantFoldTable[kind::FLOATINGPOINT_ISPOS] = constantFold::isPositive;

  /******** Conversions ********/
  d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] =
      constantFold::convertFromIEEEBitVectorLiteral;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] =
      constantFold::constantConvert;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_REAL] =
      constantFold::convertFromRealLiteral;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] =
      constantFold::convertFromSBV;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] =
      constantFold::convertFromUBV;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_UBV] = constantFold::convertToUBV;
  d_constantFoldTable[kind::FLOATINGPOINT_TO_SBV] = constantFold::convertToSBV;
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
      Debug("fp-rewrite") << "TheoryFpRewriter::preRewrite(): before " << node << std::endl;
      Debug("fp-rewrite") << "TheoryFpRewriter::preRewrite(): after  "
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
      Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): before " << node << std::endl;
      Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): after  "
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

      if (allChildrenConst) {
	RewriteStatus rs = REWRITE_DONE;    // This is a bit messy because
        Node rn = res.d_node;  // RewriteResponse is too functional..

        if (apartFromRoundingMode) {
          if (!(res.d_node.getKind() == kind::EQUAL)
              &&  // Avoid infinite recursion...
              !(res.d_node.getKind() == kind::ROUNDINGMODE_BITBLAST))
          {  // Don't eliminate the bit-blast
            // We are close to being able to constant fold this
            // and in many cases the rounding mode really doesn't matter.
            // So we can try brute forcing our way through them.

            NodeManager *nm = NodeManager::currentNM();

	    Node RNE(nm->mkConst(roundNearestTiesToEven));
	    Node RNA(nm->mkConst(roundNearestTiesToAway));
	    Node RTZ(nm->mkConst(roundTowardPositive));
	    Node RTN(nm->mkConst(roundTowardNegative));
	    Node RTP(nm->mkConst(roundTowardZero));

            TNode RM(res.d_node[0]);

            Node wRNE(res.d_node.substitute(RM, TNode(RNE)));
            Node wRNA(res.d_node.substitute(RM, TNode(RNA)));
            Node wRTZ(res.d_node.substitute(RM, TNode(RTZ)));
            Node wRTN(res.d_node.substitute(RM, TNode(RTN)));
            Node wRTP(res.d_node.substitute(RM, TNode(RTP)));

            rs = REWRITE_AGAIN_FULL;
	    rn = nm->mkNode(kind::ITE,
			    nm->mkNode(kind::EQUAL, RM, RNE),
			    wRNE,
			    nm->mkNode(kind::ITE,
				       nm->mkNode(kind::EQUAL, RM, RNA),
				       wRNA,
				       nm->mkNode(kind::ITE,
						  nm->mkNode(kind::EQUAL, RM, RTZ),
						  wRTZ,
						  nm->mkNode(kind::ITE,
							     nm->mkNode(kind::EQUAL, RM, RTN),
							     wRTN,
							     wRTP))));
	  }
	} else {
          RewriteResponse tmp =
              d_constantFoldTable[res.d_node.getKind()](res.d_node, false);
          rs = tmp.d_status;
          rn = tmp.d_node;
        }

	RewriteResponse constRes(rs,rn);

        if (constRes.d_node != res.d_node)
        {
          Debug("fp-rewrite")
              << "TheoryFpRewriter::postRewrite(): before constant fold "
              << res.d_node << std::endl;
          Debug("fp-rewrite")
              << "TheoryFpRewriter::postRewrite(): after constant fold "
              << constRes.d_node << std::endl;
        }

        return constRes;
      }
    }

    return res;
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */


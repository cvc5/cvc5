/*********************                                                        */
/*! \file theory_fp_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Paul Meng, Tim King
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
 **          (fp.abs (fp.neg x)) --> (fp.abs x)
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

#include "base/cvc4_assert.h"
#include "theory/fp/theory_fp_rewriter.h"

namespace CVC4 {
namespace theory {
namespace fp {

namespace rewrite {
  /** Rewrite rules **/
  template <RewriteFunction first, RewriteFunction second>
  RewriteResponse then (TNode node, bool isPreRewrite) {
    RewriteResponse result(first(node, isPreRewrite));

    if (result.status == REWRITE_DONE) {
      return second(result.node, isPreRewrite);
    } else {
      return result;
    }
  }

  RewriteResponse notFP (TNode node, bool) {
    Unreachable("non floating-point kind (%d) in floating point rewrite?",node.getKind());
  }

  RewriteResponse identity (TNode node, bool) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse type (TNode node, bool) {
    Unreachable("sort kind (%d) found in expression?",node.getKind());
  }

  RewriteResponse removeDoubleNegation (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_NEG);
    if (node[0].getKind() == kind::FLOATINGPOINT_NEG) {
      RewriteResponse(REWRITE_AGAIN, node[0][0]);
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
    Assert(k == kind::FLOATINGPOINT_EQ ||
	   k == kind::FLOATINGPOINT_GEQ ||
	   k == kind::FLOATINGPOINT_LEQ ||
	   k == kind::FLOATINGPOINT_GT ||
	   k == kind::FLOATINGPOINT_LT);


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

  RewriteResponse removed (TNode node, bool) {  
    Unreachable("kind (%s) should have been removed?",kindToString(node.getKind()).c_str());
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
    Assert(tn == node[1].getType(true));   // Should be ensured by the typing rules

    if (node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
    } else if (!isPreRewrite && (node[0] > node[1])) {
	Node normal = NodeManager::currentNM()->mkNode(kind::EQUAL,node[1],node[0]);
	return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }


  // Note these cannot be assumed to be symmetric for +0/-0, thus no symmetry reorder
  RewriteResponse compactMinMax (TNode node, bool isPreRewrite) {
#ifdef CVC4_ASSERTIONS
    Kind k = node.getKind();
    Assert((k == kind::FLOATINGPOINT_MIN) || (k == kind::FLOATINGPOINT_MAX) ||
	   (k == kind::FLOATINGPOINT_MIN_TOTAL) || (k == kind::FLOATINGPOINT_MAX_TOTAL));
#endif
    if (node[0] == node[1]) {
      return RewriteResponse(REWRITE_DONE, node[0]);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }


  RewriteResponse reorderFPEquality (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_EQ);
    Assert(!isPreRewrite);    // Likely redundant in pre-rewrite

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
    Assert(!isPreRewrite);    // Likely redundant in pre-rewrite

    if (node[1] > node[2]) {
      Node normal = NodeManager::currentNM()->mkNode(k,node[0],node[2],node[1]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse reorderFMA (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_FMA);
    Assert(!isPreRewrite);    // Likely redundant in pre-rewrite

    if (node[1] > node[2]) {
      Node normal = NodeManager::currentNM()->mkNode(kind::FLOATINGPOINT_FMA,node[0],node[2],node[1],node[3]);
      return RewriteResponse(REWRITE_DONE, normal);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
  }

  RewriteResponse removeSignOperations (TNode node, bool isPreRewrite) {
    Assert(node.getKind() == kind::FLOATINGPOINT_ISN   ||
	   node.getKind() == kind::FLOATINGPOINT_ISSN  ||
	   node.getKind() == kind::FLOATINGPOINT_ISZ   ||
	   node.getKind() == kind::FLOATINGPOINT_ISINF ||
	   node.getKind() == kind::FLOATINGPOINT_ISNAN);
    Assert(node.getNumChildren() == 1);

    Kind childKind(node[0].getKind());

    if ((childKind == kind::FLOATINGPOINT_NEG) ||
	(childKind == kind::FLOATINGPOINT_ABS)) {

      Node rewritten = NodeManager::currentNM()->mkNode(node.getKind(),node[0][0]);
      return RewriteResponse(REWRITE_AGAIN, rewritten);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    } 
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
    Unreachable("Equality of unknown type");
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


};  /* CVC4::theory::fp::constantFold */


RewriteFunction TheoryFpRewriter::preRewriteTable[kind::LAST_KIND]; 
RewriteFunction TheoryFpRewriter::postRewriteTable[kind::LAST_KIND]; 
RewriteFunction TheoryFpRewriter::constantFoldTable[kind::LAST_KIND]; 


  /**
   * Initialize the rewriter.
   */
  void TheoryFpRewriter::init() {

    /* Set up the pre-rewrite dispatch table */
    for (unsigned i = 0; i < kind::LAST_KIND; ++i) {
      preRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    preRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    preRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity; 

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    //preRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    preRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;
      
    /******** Operations ********/
    preRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    preRewriteTable[kind::FLOATINGPOINT_PLUS] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_SUB] = rewrite::convertSubtractionToAddition;
    preRewriteTable[kind::FLOATINGPOINT_MULT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::compactMinMax;
    preRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::compactMinMax;
    preRewriteTable[kind::FLOATINGPOINT_MIN_TOTAL] = rewrite::compactMinMax;
    preRewriteTable[kind::FLOATINGPOINT_MAX_TOTAL] = rewrite::compactMinMax;

    /******** Comparisons ********/
    preRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::then<rewrite::breakChain,rewrite::ieeeEqToEq>;
    preRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::breakChain;
    preRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::breakChain;
    preRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::then<rewrite::breakChain,rewrite::geqToleq>;
    preRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::then<rewrite::breakChain,rewrite::gtTolt>;

    /******** Classifications ********/
    preRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::identity;  
    preRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISNEG] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_ISPOS] = rewrite::identity;

    /******** Conversions ********/
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::removed;
    preRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] = rewrite::identity;

    /******** Variables ********/
    preRewriteTable[kind::VARIABLE] = rewrite::variable;
    preRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;
    preRewriteTable[kind::SKOLEM] = rewrite::variable;

    preRewriteTable[kind::EQUAL] = rewrite::equal;




    /* Set up the post-rewrite dispatch table */
    for (unsigned i = 0; i < kind::LAST_KIND; ++i) {
      postRewriteTable[i] = rewrite::notFP;
    }

    /******** Constants ********/
    /* No rewriting possible for constants */
    postRewriteTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    postRewriteTable[kind::CONST_ROUNDINGMODE] = rewrite::identity; 

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    //postRewriteTable[kind::ROUNDINGMODE_TYPE] = rewrite::type;
    postRewriteTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;
      
    /******** Operations ********/
    postRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ABS] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_NEG] = rewrite::removeDoubleNegation;
    postRewriteTable[kind::FLOATINGPOINT_PLUS] = rewrite::reorderBinaryOperation;
    postRewriteTable[kind::FLOATINGPOINT_SUB] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_MULT] = rewrite::reorderBinaryOperation;
    postRewriteTable[kind::FLOATINGPOINT_DIV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_FMA] = rewrite::reorderFMA;
    postRewriteTable[kind::FLOATINGPOINT_SQRT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_REM] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_RTI] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_MIN] = rewrite::compactMinMax;
    postRewriteTable[kind::FLOATINGPOINT_MAX] = rewrite::compactMinMax;
    postRewriteTable[kind::FLOATINGPOINT_MIN_TOTAL] = rewrite::compactMinMax;
    postRewriteTable[kind::FLOATINGPOINT_MAX_TOTAL] = rewrite::compactMinMax;

    /******** Comparisons ********/
    postRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::removed;

    /******** Classifications ********/
    postRewriteTable[kind::FLOATINGPOINT_ISN] = rewrite::removeSignOperations;
    postRewriteTable[kind::FLOATINGPOINT_ISSN] = rewrite::removeSignOperations;
    postRewriteTable[kind::FLOATINGPOINT_ISZ] = rewrite::removeSignOperations;
    postRewriteTable[kind::FLOATINGPOINT_ISINF] = rewrite::removeSignOperations;
    postRewriteTable[kind::FLOATINGPOINT_ISNAN] = rewrite::removeSignOperations;
    postRewriteTable[kind::FLOATINGPOINT_ISNEG] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_ISPOS] = rewrite::identity;

    /******** Conversions ********/
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] = rewrite::identity;

    /******** Variables ********/
    postRewriteTable[kind::VARIABLE] = rewrite::variable;
    postRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;
    postRewriteTable[kind::SKOLEM] = rewrite::variable;

    postRewriteTable[kind::EQUAL] = rewrite::equal;




    /* Set up the post-rewrite constant fold table */
    for (unsigned i = 0; i < kind::LAST_KIND; ++i) {
      // Note that this is identity, not notFP
      // Constant folding is called after post-rewrite
      // So may have to deal with cases of things being
      // re-written to non-floating-point sorts (i.e. true).
      constantFoldTable[i] = rewrite::identity;
    }

    /******** Constants ********/
    /* Already folded! */
    constantFoldTable[kind::CONST_FLOATINGPOINT] = rewrite::identity;
    constantFoldTable[kind::CONST_ROUNDINGMODE] = rewrite::identity; 

    /******** Sorts(?) ********/
    /* These kinds should only appear in types */
    constantFoldTable[kind::FLOATINGPOINT_TYPE] = rewrite::type;
      
    /******** Operations ********/
    constantFoldTable[kind::FLOATINGPOINT_FP] = constantFold::fpLiteral;
    constantFoldTable[kind::FLOATINGPOINT_ABS] = constantFold::abs;
    constantFoldTable[kind::FLOATINGPOINT_NEG] = constantFold::neg;
    constantFoldTable[kind::FLOATINGPOINT_PLUS] = constantFold::plus;
    constantFoldTable[kind::FLOATINGPOINT_SUB] = rewrite::removed;
    constantFoldTable[kind::FLOATINGPOINT_MULT] = constantFold::mult;
    constantFoldTable[kind::FLOATINGPOINT_DIV] = constantFold::div;
    constantFoldTable[kind::FLOATINGPOINT_FMA] = constantFold::fma;
    constantFoldTable[kind::FLOATINGPOINT_SQRT] = constantFold::sqrt;
    constantFoldTable[kind::FLOATINGPOINT_REM] = constantFold::rem;
    constantFoldTable[kind::FLOATINGPOINT_RTI] = constantFold::rti;
    constantFoldTable[kind::FLOATINGPOINT_MIN] = constantFold::min;
    constantFoldTable[kind::FLOATINGPOINT_MAX] = constantFold::max;
    constantFoldTable[kind::FLOATINGPOINT_MIN_TOTAL] = constantFold::minTotal;
    constantFoldTable[kind::FLOATINGPOINT_MAX_TOTAL] = constantFold::maxTotal;

    /******** Comparisons ********/
    constantFoldTable[kind::FLOATINGPOINT_EQ] = rewrite::removed;
    constantFoldTable[kind::FLOATINGPOINT_LEQ] = constantFold::leq;
    constantFoldTable[kind::FLOATINGPOINT_LT] = constantFold::lt;
    constantFoldTable[kind::FLOATINGPOINT_GEQ] = rewrite::removed;
    constantFoldTable[kind::FLOATINGPOINT_GT] = rewrite::removed;

    /******** Classifications ********/
    constantFoldTable[kind::FLOATINGPOINT_ISN] = constantFold::isNormal;
    constantFoldTable[kind::FLOATINGPOINT_ISSN] = constantFold::isSubnormal;
    constantFoldTable[kind::FLOATINGPOINT_ISZ] = constantFold::isZero;
    constantFoldTable[kind::FLOATINGPOINT_ISINF] = constantFold::isInfinite;
    constantFoldTable[kind::FLOATINGPOINT_ISNAN] = constantFold::isNaN;
    constantFoldTable[kind::FLOATINGPOINT_ISNEG] = constantFold::isNegative;
    constantFoldTable[kind::FLOATINGPOINT_ISPOS] = constantFold::isPositive;

    /******** Conversions ********/
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = constantFold::convertFromIEEEBitVectorLiteral;
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = constantFold::constantConvert;
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_REAL] = constantFold::convertFromRealLiteral;
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = constantFold::convertFromSBV;
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = constantFold::convertFromUBV;
    constantFoldTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::removed;
    constantFoldTable[kind::FLOATINGPOINT_TO_UBV] = constantFold::convertToUBV;
    constantFoldTable[kind::FLOATINGPOINT_TO_SBV] = constantFold::convertToSBV;
    constantFoldTable[kind::FLOATINGPOINT_TO_REAL] = constantFold::convertToReal;
    constantFoldTable[kind::FLOATINGPOINT_TO_UBV_TOTAL] = constantFold::convertToUBVTotal;
    constantFoldTable[kind::FLOATINGPOINT_TO_SBV_TOTAL] = constantFold::convertToSBVTotal;
    constantFoldTable[kind::FLOATINGPOINT_TO_REAL_TOTAL] = constantFold::convertToRealTotal;

    /******** Variables ********/
    constantFoldTable[kind::VARIABLE] = rewrite::variable;
    constantFoldTable[kind::BOUND_VARIABLE] = rewrite::variable;

    constantFoldTable[kind::EQUAL] = constantFold::equal;



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
    RewriteResponse res = preRewriteTable [node.getKind()] (node, true);
    if (res.node != node) {
      Debug("fp-rewrite") << "TheoryFpRewriter::preRewrite(): before " << node << std::endl;
      Debug("fp-rewrite") << "TheoryFpRewriter::preRewrite(): after  " << res.node << std::endl;
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
    RewriteResponse res = postRewriteTable [node.getKind()] (node, false);
    if (res.node != node) {
      Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): before " << node << std::endl;
      Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): after  " << res.node << std::endl;
    }

    if (res.status == REWRITE_DONE) {
      bool allChildrenConst = true;
      bool apartFromRoundingMode = false;
      bool apartFromPartiallyDefinedArgument = false;
      for (Node::const_iterator i = res.node.begin();
	   i != res.node.end();
	   ++i) {

	if ((*i).getMetaKind() != kind::metakind::CONSTANT) {
	  if ((*i).getType().isRoundingMode() && !apartFromRoundingMode) {
	    apartFromRoundingMode = true;
	  } else if ((res.node.getKind() == kind::FLOATINGPOINT_MIN_TOTAL ||
		      res.node.getKind() == kind::FLOATINGPOINT_MAX_TOTAL ||
		      res.node.getKind() == kind::FLOATINGPOINT_TO_UBV_TOTAL ||
		      res.node.getKind() == kind::FLOATINGPOINT_TO_SBV_TOTAL ||
		      res.node.getKind() == kind::FLOATINGPOINT_TO_REAL_TOTAL) &&
		     ((*i).getType().isBitVector() ||
		      (*i).getType().isReal()) &&
		     !apartFromPartiallyDefinedArgument) {
	    apartFromPartiallyDefinedArgument = true;
	  } else {
	    allChildrenConst = false;
	    break;
	  }
	}
      }

      if (allChildrenConst) {
	RewriteStatus rs = REWRITE_DONE;    // This is a bit messy because
	Node rn = res.node;                 // RewriteResponse is too functional..

	if (apartFromRoundingMode) {
	  if (!(res.node.getKind() == kind::EQUAL)) {  // Avoid infinite recursion...
	    // We are close to being able to constant fold this
	    // and in many cases the rounding mode really doesn't matter.
	    // So we can try brute forcing our way through them.

	    NodeManager *nm = NodeManager::currentNM();

	    Node RNE(nm->mkConst(roundNearestTiesToEven));
	    Node RNA(nm->mkConst(roundNearestTiesToAway));
	    Node RTZ(nm->mkConst(roundTowardPositive));
	    Node RTN(nm->mkConst(roundTowardNegative));
	    Node RTP(nm->mkConst(roundTowardZero));

	    TNode RM(res.node[0]);

	    Node wRNE(res.node.substitute(RM, TNode(RNE)));
	    Node wRNA(res.node.substitute(RM, TNode(RNA)));
	    Node wRTZ(res.node.substitute(RM, TNode(RTZ)));
	    Node wRTN(res.node.substitute(RM, TNode(RTN)));
	    Node wRTP(res.node.substitute(RM, TNode(RTP)));


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
	  RewriteResponse tmp = constantFoldTable [res.node.getKind()] (res.node, false);
	  rs = tmp.status;
	  rn = tmp.node;
	}

	RewriteResponse constRes(rs,rn);

	if (constRes.node != res.node) {
	  Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): before constant fold " << res.node << std::endl;
	  Debug("fp-rewrite") << "TheoryFpRewriter::postRewrite(): after constant fold " << constRes.node << std::endl;
	}

	return constRes;
      }
    }

    return res;
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */


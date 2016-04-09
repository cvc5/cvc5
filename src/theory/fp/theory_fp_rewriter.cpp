/*********************                                                        */
/*! \file theory_fp_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Tim King, Clark Barrett
 ** Copyright (c) 2013  University of Oxford
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Rewrite rules for floating point theories. ]]
 **
 ** \todo [[ Constant folding
 **          Push negations up through arithmetic operators (include max and min? maybe not due to +0/-0)
 **          classifications to normal tests (maybe)
 **          (= x (fp.neg x)) --> (isNaN x)
 **          (fp.eq x (fp.neg x)) --> (isZero x)   (previous and reorganise should be sufficient)
 **          (fp.eq x const) --> various = depending on const 
 **          (fp.abs (fp.neg x)) --> (fp.abs x)
 **          (fp.isPositive (fp.neg x)) --> (fp.isNegative x)
 **          (fp.isNegative (fp.neg x)) --> (fp.isPositive x)
 **          (fp.isPositive (fp.abs x)) --> (not (isNaN x))
 **          (fp.isNegative (fp.abs x)) --> false
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

  RewriteResponse notFP (TNode node, bool) {
    Unreachable("non floating-point kind (%d) in floating point rewrite?",node.getKind());
  }

  RewriteResponse identity (TNode node, bool) {
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse type (TNode node, bool) {
    Unreachable("sort kind (%d) found in expression?",node.getKind());
    return RewriteResponse(REWRITE_DONE, node);
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
    Unreachable("kind (%d) should have been removed?",node.getKind());
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse variable (TNode node, bool) {  
    // We should only get floating point and rounding mode variables to rewrite.
    TypeNode tn = node.getType(true);
    Assert(tn.isFloatingPoint() || tn.isRoundingMode());
 
    // Not that we do anything with them...
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse equal (TNode node, bool isPreRewrite) {  
    // We should only get equalities of floating point or rounding mode types.
    Assert(node.getKind() == kind::EQUAL);

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

  RewriteResponse convertFromRealLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_REAL);

    // \todo Honour the rounding mode and work for something other than doubles!

    if (node[1].getKind() == kind::CONST_RATIONAL) {
      TNode op = node.getOperator();
      const FloatingPointToFPReal &param = op.getConst<FloatingPointToFPReal>();
      Node lit =
	NodeManager::currentNM()->mkConst(FloatingPoint(param.t.exponent(),
							param.t.significand(),
							node[1].getConst<Rational>().getDouble()));
      
      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertFromIEEEBitVectorLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR);

    // \todo Handle arbitrary length bit vectors without using strings!

    if (node[0].getKind() == kind::CONST_BITVECTOR) {
      TNode op = node.getOperator();
      const FloatingPointToFPIEEEBitVector &param = op.getConst<FloatingPointToFPIEEEBitVector>();
      const BitVector &bv = node[0].getConst<BitVector>();
      std::string bitString(bv.toString());

      Node lit =
	NodeManager::currentNM()->mkConst(FloatingPoint(param.t.exponent(),
							param.t.significand(),
							bitString));

      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  RewriteResponse convertFromLiteral (TNode node, bool) {
    Assert(node.getKind() == kind::FLOATINGPOINT_FP);

    // \todo Handle arbitrary length bit vectors without using strings!

    if ((node[0].getKind() == kind::CONST_BITVECTOR) &&
	(node[1].getKind() == kind::CONST_BITVECTOR) &&
	(node[2].getKind() == kind::CONST_BITVECTOR)) {

      BitVector bv(node[0].getConst<BitVector>());
      bv = bv.concat(node[1].getConst<BitVector>());
      bv = bv.concat(node[2].getConst<BitVector>());

      std::string bitString(bv.toString());
      std::reverse(bitString.begin(), bitString.end());

      // +1 to support the hidden bit
      Node lit =
	NodeManager::currentNM()->mkConst(FloatingPoint(node[1].getConst<BitVector>().getSize(),
							node[2].getConst<BitVector>().getSize() + 1,
							bitString));

      return RewriteResponse(REWRITE_DONE, lit);
    } else {
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  // Note these cannot be assumed to be symmetric for +0/-0, thus no symmetry reorder
  RewriteResponse compactMinMax (TNode node, bool isPreRewrite) {
#ifdef CVC4_ASSERTIONS
    Kind k = node.getKind();
    Assert((k == kind::FLOATINGPOINT_MIN) || (k == kind::FLOATINGPOINT_MAX));
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

RewriteFunction TheoryFpRewriter::preRewriteTable[kind::LAST_KIND]; 
RewriteFunction TheoryFpRewriter::postRewriteTable[kind::LAST_KIND]; 


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

    /******** Comparisons ********/
    preRewriteTable[kind::FLOATINGPOINT_EQ] = rewrite::ieeeEqToEq;
    preRewriteTable[kind::FLOATINGPOINT_LEQ] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_LT] = rewrite::identity;
    preRewriteTable[kind::FLOATINGPOINT_GEQ] = rewrite::geqToleq;
    preRewriteTable[kind::FLOATINGPOINT_GT] = rewrite::gtTolt;

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

    /******** Variables ********/
    preRewriteTable[kind::VARIABLE] = rewrite::variable;
    preRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;

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
    postRewriteTable[kind::FLOATINGPOINT_FP] = rewrite::convertFromLiteral;
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
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_IEEE_BITVECTOR] = rewrite::convertFromIEEEBitVectorLiteral;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_FLOATINGPOINT] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_REAL] = rewrite::convertFromRealLiteral;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_SIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_UNSIGNED_BITVECTOR] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_FP_GENERIC] = rewrite::removed;
    postRewriteTable[kind::FLOATINGPOINT_TO_UBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_SBV] = rewrite::identity;
    postRewriteTable[kind::FLOATINGPOINT_TO_REAL] = rewrite::identity;

    /******** Variables ********/
    postRewriteTable[kind::VARIABLE] = rewrite::variable;
    postRewriteTable[kind::BOUND_VARIABLE] = rewrite::variable;

    postRewriteTable[kind::EQUAL] = rewrite::equal;


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
    return res;
  }


}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */


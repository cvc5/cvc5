/*********************                                                        */
/*! \file arith_rewriter.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "expr/node.h"
#include "util/rational.h"
#include "theory/arith/arith_constants.h"

#ifndef __CVC4__THEORY__ARITH__REWRITER_H
#define __CVC4__THEORY__ARITH__REWRITER_H

namespace CVC4 {
namespace theory {
namespace arith {


/***********************************************/
/***************** Normal Form *****************/
/***********************************************/
/***********************************************/

/**
 * Normal form for predicates:
 *    TRUE
 *    FALSE
 *    v |><| b
 *    p |><| b
 *    (+ p_1 .. p_N)  |><| b
 *  where
 *   1) b is of type CONST_RATIONAL
 *   2) |><| is of kind <, <=, =, >= or >
 *   3) p, p_i is in PNF,
 *   4) p.M >= 2
 *   5) p_i's are in strictly ascending <p,
 *   6) N >= 2,
 *   7) the kind of (+ p_1 .. p_N) is an N arity PLUS,
 *   8) p.d, p_1.d are 1,
 *   9) v has metakind variable, and
 *
 * PNF(t):
 *    (* d v_1 v_2 ... v_M)
 *  where
 *   1) d is of type CONST_RATIONAL,
 *   2) d != 0,
 *   4) M>=1,
 *   5) v_i are of metakind VARIABLE,
 *   6) v_i are in increasing (not strict) nodeOrder, and
 *   7) the kind of t is an M+1 arity MULT.
 *
 * <p is defined over PNF as follows (skipping some symmetry):
 *   cmp( (* d v_1 v_2 ... v_M), (* d' v'_1 v'_2 ... v'_M'):
 *      if(M == M'):
 *      then tupleCompare(v_i, v'_i)
 *      else M -M'
 *
 * Rewrite Normal Form for Terms:
 *    b
 *    v
 *    (+ c p_1 p_2 ... p_N)  |  not(N=1 and c=0 and p_1.d=1)
 *  where
 *   1) b,c is of type CONST_RATIONAL,
 *   3) p_i is in PNF,
 *   4) N >= 1
 *   5) the kind of (+ c p_1 p_2 ... p_N) is an N+1 arity PLUS,
 *   6) and p_i's are in strictly <p.
 *
 */

class ArithRewriter{
private:
  ArithConstants* d_constants;

  //This is where the core of the work is done for rewriteAtom
  //With a few additional checks done by rewriteAtom
  Node rewriteAtomCore(TNode atom);
  Node rewriteAtom(TNode atom);

  Node rewriteTerm(TNode t);
  Node rewriteMult(TNode t);
  Node rewritePlus(TNode t);
  Node rewriteMinus(TNode t);
  Node makeSubtractionNode(TNode l, TNode r);
  Node makeUnaryMinusNode(TNode n);


  Node var2pnf(TNode variable);

  Node multPnfByNonZero(TNode pnf, Rational& q);

  Node rewriteConstantDiv(TNode t);
  void sortAndCombineCoefficients(std::vector<Node>& pnfs);


public:
  ArithRewriter(ArithConstants* ac) :
    d_constants(ac)
  {}
  Node rewrite(TNode t);

};


}; /* namesapce arith */
}; /* namespace theory */
}; /* namespace CVC4 */

#endif /* __CVC4__THEORY__ARITH__REWRITER_H */

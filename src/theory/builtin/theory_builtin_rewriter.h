/*********************                                                        */
/*! \file theory_builtin_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H
#define __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H

#include "theory/rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltinRewriter {

  static Node blastDistinct(TNode node);
  static Node blastChain(TNode node);

public:

  static inline RewriteResponse doRewrite(TNode node) {
    switch(node.getKind()) {
    case kind::DISTINCT:
      return RewriteResponse(REWRITE_DONE, blastDistinct(node));
    case kind::CHAIN:
      return RewriteResponse(REWRITE_DONE, blastChain(node));
    default:
      return RewriteResponse(REWRITE_DONE, node);
    }
  }

  static RewriteResponse postRewrite(TNode node);

  static inline RewriteResponse preRewrite(TNode node) {
    return doRewrite(node);
  }

  static inline void init() {}
  static inline void shutdown() {}

// conversions between lambdas and arrays
private:  
  /** recursive helper for getLambdaForArrayRepresentation */
  static Node getLambdaForArrayRepresentationRec( TNode a, TNode bvl, unsigned bvlIndex, 
                                                  std::unordered_map< TNode, Node, TNodeHashFunction >& visited );
  /** recursive helper for getArrayRepresentationForLambda */
  static Node getArrayRepresentationForLambdaRec( TNode n, bool reqConst, TypeNode retType );
public:
 /** Get function type for array type
  *
  * This returns the function type of terms returned by the function
  * getLambdaForArrayRepresentation( t, bvl ),
  * where t.getType()=atn.
  *
  * bvl should be a bound variable list whose variables correspond in-order
  * to the index types of the (curried) Array type. For example, a bound
  * variable list bvl whose variables have types (Int, Real) can be given as
  * input when paired with atn = (Array Int (Array Real Bool)), or (Array Int
  * (Array Real (Array Bool Bool))). This function returns (-> Int Real Bool)
  * and (-> Int Real (Array Bool Bool)) respectively in these cases.
  * On the other hand, the above bvl is not a proper input for
  * atn = (Array Int (Array Bool Bool)) or (Array Int Int).
  * If the types of bvl and atn do not match, we throw an assertion failure.
  */
 static TypeNode getFunctionTypeForArrayType(TypeNode atn, Node bvl);
 /** Get array type for function type
  *
  * This returns the array type of terms returned by
  * getArrayRepresentationForLambda( t ), where t.getType()=ftn.
  */
 static TypeNode getArrayTypeForFunctionType(TypeNode ftn);
 /**
  * Given an array constant a, returns a lambda expression that it corresponds
  * to, with bound variable list bvl.
  * Examples:
  *
  * (store (storeall (Array Int Int) 2) 0 1)
  * becomes
  * ((lambda x. (ite (= x 0) 1 2))
  *
  * (store (storeall (Array Int (Array Int Int)) (storeall (Array Int Int) 4)) 0
  * (store (storeall (Array Int Int) 3) 1 2))
  * becomes
  * (lambda xy. (ite (= x 0) (ite (= x 1) 2 3) 4))
  *
  * (store (store (storeall (Array Int Bool) false) 2 true) 1 true)
  * becomes
  * (lambda x. (ite (= x 1) true (ite (= x 2) true false)))
  *
  * Notice that the return body of the lambda is rewritten to ensure that the
  * representation is canonical. Hence the last
  * example will in fact be returned as:
  * (lambda x. (ite (= x 1) true (= x 2)))
  */
 static Node getLambdaForArrayRepresentation(TNode a, TNode bvl);
 /** given a lambda expression n, returns an array term. reqConst is true if we
  * require the return value to be a constant.
   * This does the opposite direction of the examples described above.
   */
 static Node getArrayRepresentationForLambda(TNode n, bool reqConst = false);
};/* class TheoryBuiltinRewriter */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H */

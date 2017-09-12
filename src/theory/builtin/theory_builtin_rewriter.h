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
public:
  /** 
   * Given an array constant a, returns a lambda expression that it corresponds to, with bound variable list bvl. 
   * Examples:
   *
   * (store 0 1 (storeall (Array Int Int) 2)) 
   * becomes
   * ((lambda x. (ite (= x 0) 1 2))
   *
   * (store 0 (store 1 2 (storeall (Array Int Int) 3)) (storeall (Array Int (Array Int Int)) (storeall (Array Int Int) 4)))
   * becomes
   * (lambda xy. (ite (= x 0) (ite (= x 1) 2 3) 4))
   *
   * (store 1 true (store 2 true (storeall (Array Int Bool) false)))
   * becomes
   * (lambda x. (ite (= x 1) true (ite (= x 2) true false)))
   *
   * Notice that the return body of the lambda is rewritten to ensure that the representation is canonical. Hence the last
   * example will in fact be returned as:
   * (lambda x. (ite (= x 1) true (= x 2)))
   */
  static Node getLambdaForArrayRepresentation( TNode a, TNode bvl );
  /** given a lambda expression n, returns an array term. reqConst is true if we require the return value to be a constant. 
    * This does the opposite direction of the examples described above.
    */
  static Node getArrayRepresentationForLambda( TNode n, bool reqConst = false );
  /** get a canonical bound variable list for function type tn */
  static Node getLambdaBoundVarListForType( TypeNode tn, unsigned nargs );
};/* class TheoryBuiltinRewriter */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H */

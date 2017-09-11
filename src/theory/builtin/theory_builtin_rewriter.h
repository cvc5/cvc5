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

  static inline RewriteResponse postRewrite(TNode node) {
    if( node.getKind()==kind::LAMBDA ){
      Trace("builtin-rewrite") << "Rewriting lambda " << node << "..." << std::endl;
      Node anode = getArrayRepresentationForLambda( node );
      if( !anode.isNull() ){
        anode = Rewriter::rewrite( anode );
        Assert( anode.getType().isArray() );
        //must get the standard bound variable list
        Node varList = getLambdaBoundVarListForType( node.getType(), node[0].getNumChildren() );
        Node retNode = getLambdaForArrayRepresentation( anode, varList );
        if( !retNode.isNull() && retNode!=node ){
          Trace("builtin-rewrite") << "Rewrote lambda : " << std::endl;
          Trace("builtin-rewrite") << "     input  : " << node << std::endl;
          Trace("builtin-rewrite") << "     output : " << retNode << ", constant = " << retNode.isConst() << std::endl;
          Trace("builtin-rewrite") << "  array rep : " << anode << ", constant = " << anode.isConst() << std::endl;
          Assert( anode.isConst()==retNode.isConst() );
          Assert( retNode.getType()==node.getType() );
          return RewriteResponse(REWRITE_DONE, retNode);
        } 
      }else{
        Trace("builtin-rewrite-debug") << "...failed to get array representation." << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, node);
    }else{ 
      return doRewrite(node);
    }
  }

  static inline RewriteResponse preRewrite(TNode node) {
    return doRewrite(node);
  }

  static inline void init() {}
  static inline void shutdown() {}

// conversions between lambdas and arrays
private:  
  static Node getLambdaForArrayRepresentationRec( TNode a, TNode bvl, unsigned bvlIndex, 
                                                  std::unordered_map< TNode, Node, TNodeHashFunction >& visited );
public:
  /** given an array constant a, returns a lambda expression that it corresponds to, with bound variable list bvl. */
  static Node getLambdaForArrayRepresentation( TNode a, TNode bvl );
  /** given a lambda expression n, returns an array term. reqConst is true if we require the return value to be a constant. */
  static Node getArrayRepresentationForLambda( TNode n, bool reqConst = false );
  /** get a canonical bound variable list for function type tn */
  static Node getLambdaBoundVarListForType( TypeNode tn, unsigned nargs );
};/* class TheoryBuiltinRewriter */

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BUILTIN__THEORY_BUILTIN_REWRITER_H */

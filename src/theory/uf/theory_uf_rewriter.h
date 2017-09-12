/*********************                                                        */
/*! \file theory_uf_rewriter.h
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

#ifndef __CVC4__THEORY__UF__THEORY_UF_REWRITER_H
#define __CVC4__THEORY__UF__THEORY_UF_REWRITER_H

#include "theory/rewriter.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUfRewriter {

public:

  static RewriteResponse postRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
    }
    if(node.getKind() == kind::APPLY_UF) {
      if( node.getOperator().getKind() == kind::LAMBDA ){
        // resolve away the lambda
        context::Context fakeContext;
        theory::SubstitutionMap substitutions(&fakeContext);
        TNode lambda = node.getOperator();
        for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
          // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
          Assert(formal != node.end());
          // This rewrite step is important: if we have (f (f 5)) for
          // some lambda term f, we want to beta-reduce the inside (f 5)
          // application first.  Otherwise, we can end up in infinite
          // recursion, because f's formal (say "x") gives the
          // substitution "x |-> (f 5)".  Fine, the body of the lambda
          // gets (f 5) in place for x.  But since the same lambda ("f")
          // now occurs in the body, it's got the same bound var "x", so
          // substitution continues and we replace that x by (f 5).  And
          // then again.  :-(
          //
          // We need a better solution for distinguishing bound
          // variables like this, but for now, handle it by going
          // inside-out.  (Quantifiers shouldn't ever have this problem,
          // so long as the bound vars in different quantifiers are kept
          // different.)
          Node n = Rewriter::rewrite(*arg);
          substitutions.addSubstitution(*formal, n);
        }
        return RewriteResponse(REWRITE_AGAIN_FULL, substitutions.apply(lambda[1]));
      }else if( !isStdApplyUfOperator( node.getOperator() ) ){
        return RewriteResponse(REWRITE_AGAIN_FULL, getHoApplyForApplyUf(node));
      }
    }else if( node.getKind() == kind::HO_APPLY ){
      if( node[0].getKind() == kind::LAMBDA ){
        // resolve one argument of the lambda
        TNode arg = Rewriter::rewrite( node[1] );
        TNode var = node[0][0][0];
        Node new_body = node[0][1].substitute( var, arg );
        if( node[0][0].getNumChildren()>1 ){
          std::vector< Node > new_vars;
          for( unsigned i=1; i<node[0][0].getNumChildren(); i++ ){
            new_vars.push_back( node[0][0][i] );
          }
          std::vector< Node > largs;
          largs.push_back( NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, new_vars ) );
          largs.push_back( new_body );
          new_body = NodeManager::currentNM()->mkNode( kind::LAMBDA, largs );
        }
        return RewriteResponse( REWRITE_AGAIN_FULL, new_body );
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static RewriteResponse preRewrite(TNode node) {
    if(node.getKind() == kind::EQUAL) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
    }
    if(node.getKind() == kind::APPLY_UF && node.getOperator().getKind() == kind::LAMBDA) {
      // resolve away the lambda
      context::Context fakeContext;
      theory::SubstitutionMap substitutions(&fakeContext);
      TNode lambda = node.getOperator();
      for(TNode::iterator formal = lambda[0].begin(), arg = node.begin(); formal != lambda[0].end(); ++formal, ++arg) {
        // typechecking should ensure that the APPLY_UF is well-typed, correct arity, etc.
        Assert(formal != node.end());
        // This rewrite step is important: see note in postRewrite().
        Node n = Rewriter::rewrite(*arg);
        substitutions.addSubstitution(*formal, n);
      }
      return RewriteResponse(REWRITE_DONE, substitutions.apply(lambda[1]));
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  static inline void init() {}
  static inline void shutdown() {}

public: //conversion between HO_APPLY AND APPLY_UF
  // converts an APPLY_UF to a curried HO_APPLY e.g. (f a b) becomes (@ (@ f a) b)
  static Node getHoApplyForApplyUf(TNode n) {
    Assert( n.getKind()==kind::APPLY_UF );
    Node curr = n.getOperator();
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      curr = NodeManager::currentNM()->mkNode( kind::HO_APPLY, curr, n[i] );     
    }
    return curr;
  }
  // converts a curried HO_APPLY into an APPLY_UF e.g. (@ (@ f a) b) becomes (f a b)
  static Node getApplyUfForHoApply(TNode n) {
    Assert( n.getType().getNumChildren()==2 );
    std::vector< TNode > children;
    TNode curr = decomposeHoApply( n, children, true );
    // if operator is standard
    if( isStdApplyUfOperator( curr ) ){
      return NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
    }
    // cannot construct APPLY_UF if operator is partially applied or is not standard       
    return Node::null();
  }
  // gets arguments, returns operator of a curried HO_APPLY node
  static Node decomposeHoApply(TNode n, std::vector<TNode>& args, bool opInArgs = false) {
    TNode curr = n;
    while( curr.getKind() == kind::HO_APPLY ){
      args.push_back( curr[1] );
      curr = curr[0];        
    }
    if( opInArgs ){
      args.push_back( curr );
    }
    std::reverse( args.begin(), args.end() );
    return curr;
  }
  /** returns true if this node can be used as an operator of an APPLY_UF node
   * f: Int -> Int, g : Int -> Int
   * forall x : ( Int -> Int ), y : Int. (x y) = (f 0)
   * Then, f and g are standard APPLY_UF operators, but (ite C f g), (lambda x1. (f x1)) as well as variable x above are not.  
   */
  static inline bool isStdApplyUfOperator(TNode n){
    return n.isVar() && n.getKind()!=kind::BOUND_VARIABLE;
  }
};/* class TheoryUfRewriter */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_REWRITER_H */

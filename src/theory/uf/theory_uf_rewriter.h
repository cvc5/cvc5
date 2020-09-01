/*********************                                                        */
/*! \file theory_uf_rewriter.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#ifndef CVC4__THEORY__UF__THEORY_UF_REWRITER_H
#define CVC4__THEORY__UF__THEORY_UF_REWRITER_H

#include "expr/node_algorithm.h"
#include "options/uf_options.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"
#include "theory/theory_rewriter.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUfRewriter : public TheoryRewriter
{
 public:
  RewriteResponse postRewrite(TNode node) override
  {
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
        Trace("uf-ho-beta")
          << "uf-ho-beta : beta-reducing all args of : " << node << "\n";
        TNode lambda = node.getOperator();
        Node ret;
        // build capture-avoiding substitution since in HOL shadowing may have
        // been introduced
        if (options::ufHo())
        {
          std::vector<Node> vars;
          std::vector<Node> subs;
          for (const Node& v : lambda[0])
          {
            vars.push_back(v);
          }
          for (const Node& s : node)
          {
            subs.push_back(s);
          }
          if (Trace.isOn("uf-ho-beta"))
          {
            Trace("uf-ho-beta") << "uf-ho-beta: ..sub of " << subs.size()
                                << " vars into " << subs.size() << " terms :\n";
            for (unsigned i = 0, size = subs.size(); i < size; ++i)
            {
              Trace("uf-ho-beta") << "uf-ho-beta: .... " << vars[i] << " |-> "
                                  << subs[i] << "\n";
            }
          }
          ret = expr::substituteCaptureAvoiding(lambda[1], vars, subs);
          Trace("uf-ho-beta") << "uf-ho-beta : ..result : " << ret << "\n";
        }
        else
        {
          std::vector<TNode> vars;
          std::vector<TNode> subs;
          for (const TNode& v : lambda[0])
          {
            vars.push_back(v);
          }
          for (const TNode& s : node)
          {
            subs.push_back(s);
          }
          ret = lambda[1].substitute(
              vars.begin(), vars.end(), subs.begin(), subs.end());
        }
        return RewriteResponse(REWRITE_AGAIN_FULL, ret);
      }else if( !canUseAsApplyUfOperator( node.getOperator() ) ){
        return RewriteResponse(REWRITE_AGAIN_FULL, getHoApplyForApplyUf(node));
      }
    }else if( node.getKind() == kind::HO_APPLY ){
      if( node[0].getKind() == kind::LAMBDA ){
        // resolve one argument of the lambda
        Trace("uf-ho-beta")
            << "uf-ho-beta : beta-reducing one argument of : " << node[0]
            << " with " << node[1] << "\n";

        // reconstruct the lambda first to avoid variable shadowing
        Node new_body = node[0][1];
        if( node[0][0].getNumChildren()>1 ){
          std::vector< Node > new_vars;
          for( unsigned i=1; i<node[0][0].getNumChildren(); i++ ){
            new_vars.push_back( node[0][0][i] );
          }
          std::vector< Node > largs;
          largs.push_back( NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, new_vars ) );
          largs.push_back( new_body );
          new_body = NodeManager::currentNM()->mkNode( kind::LAMBDA, largs );
          Trace("uf-ho-beta")
            << "uf-ho-beta : ....new lambda : " << new_body << "\n";
        }

        // build capture-avoiding substitution since in HOL shadowing may have
        // been introduced
        if (options::ufHo())
        {
          Node arg = Rewriter::rewrite(node[1]);
          Node var = node[0][0][0];
          new_body = expr::substituteCaptureAvoiding(new_body, var, arg);
        }
        else
        {
          TNode arg = Rewriter::rewrite(node[1]);
          TNode var = node[0][0][0];
          new_body = new_body.substitute(var, arg);
        }
        Trace("uf-ho-beta")
            << "uf-ho-beta : ..new body : " << new_body << "\n";
        return RewriteResponse( REWRITE_AGAIN_FULL, new_body );
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

  RewriteResponse preRewrite(TNode node) override
  {
    if(node.getKind() == kind::EQUAL) {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      } else if(node[0].isConst() && node[1].isConst()) {
        // uninterpreted constants are all distinct
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }

public: //conversion between HO_APPLY AND APPLY_UF
  // converts an APPLY_UF to a curried HO_APPLY e.g. (f a b) becomes (@ (@ f a) b)
  static Node getHoApplyForApplyUf(TNode n) {
    Assert(n.getKind() == kind::APPLY_UF);
    Node curr = n.getOperator();
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      curr = NodeManager::currentNM()->mkNode( kind::HO_APPLY, curr, n[i] );     
    }
    return curr;
  }
  // converts a curried HO_APPLY into an APPLY_UF e.g. (@ (@ f a) b) becomes (f a b)
  static Node getApplyUfForHoApply(TNode n) {
    Assert(n.getType().getNumChildren() == 2);
    std::vector< TNode > children;
    TNode curr = decomposeHoApply( n, children, true );
    // if operator is standard
    if( canUseAsApplyUfOperator( curr ) ){
      return NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
    }
    // cannot construct APPLY_UF if operator is partially applied or is not standard       
    return Node::null();
  }
  /**
   * Given a curried HO_APPLY term n, this method adds its arguments into args
   * and returns its operator. If the argument opInArgs is true, then we add
   * its operator to args.
   */
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
  /** returns true if this node can be used as an operator of an APPLY_UF node.  In higher-order logic,
   * terms can have function types and not just variables. 
   * Currently, we want only free variables to be used as operators of APPLY_UF nodes. This is motivated by
   * E-matching, ite-lifting among other things.  For example:
   * f: Int -> Int, g : Int -> Int
   * forall x : ( Int -> Int ), y : Int. (x y) = (f 0)
   * Then, f and g can be used as APPLY_UF operators, but (ite C f g), (lambda x1. (f x1)) as well as the variable x above are not.
   */
  static inline bool canUseAsApplyUfOperator(TNode n){
    return n.isVar();
  }
}; /* class TheoryUfRewriter */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__UF__THEORY_UF_REWRITER_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of separation logic rewriter.
 */

#include "theory/sep/theory_sep_rewriter.h"

#include "expr/attribute.h"
#include "expr/emptyset.h"
#include "options/sep_options.h"
#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace sep {

void TheorySepRewriter::getStarChildren( Node n, std::vector< Node >& s_children, std::vector< Node >& ns_children ){
  Assert(n.getKind() == kind::SEP_STAR);
  Node tr = NodeManager::currentNM()->mkConst( true );
  for( unsigned i=0; i<n.getNumChildren(); i++ ){
    if( n[i].getKind()==kind::SEP_EMP ){
      s_children.push_back( n[i] );
    }else if( n[i].getKind()==kind::SEP_STAR ){
      getStarChildren( n[i], s_children, ns_children );
    }else if( n[i].getKind()==kind::SEP_PTO ){
      s_children.push_back( n[i] );
    }else{
      std::vector< Node > temp_s_children;
      getAndChildren( n[i], temp_s_children, ns_children );
      Node to_add;
      if( temp_s_children.size()==0 ){
        if( std::find( s_children.begin(), s_children.end(), tr )==s_children.end() ){
          to_add = tr;
        }
      }else if( temp_s_children.size()==1 ){
        to_add = temp_s_children[0];
      }else{
        to_add = NodeManager::currentNM()->mkNode( kind::AND, temp_s_children );
      }
      if( !to_add.isNull() ){
        //flatten star
        if( to_add.getKind()==kind::SEP_STAR ){
          getStarChildren( to_add, s_children, ns_children );
        }else if( to_add.getKind()!=kind::SEP_EMP || s_children.empty() ){  //remove sep emp
          s_children.push_back( to_add );
        }
      }
    }
  }
}

void TheorySepRewriter::getAndChildren( Node n, std::vector< Node >& s_children, std::vector< Node >& ns_children ) {
  if( n.getKind()==kind::AND ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      getAndChildren( n[i], s_children, ns_children );
    }
  }else{
    std::map< Node, bool > visited;
    if( isSpatial( n, visited ) ){
      if( std::find( s_children.begin(), s_children.end(), n )==s_children.end() ){
        s_children.push_back( n );
      }
    }else{
      if( std::find( ns_children.begin(), ns_children.end(), n )==ns_children.end() ){
        if( n!=NodeManager::currentNM()->mkConst(true) ){
          ns_children.push_back( n );
        }
      }
    }
  }
}

bool TheorySepRewriter::isSpatial( Node n, std::map< Node, bool >& visited ) {
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==kind::SEP_STAR || n.getKind()==kind::SEP_PTO || n.getKind()==kind::SEP_EMP || n.getKind()==kind::SEP_LABEL ){
      return true;
    }else if( n.getType().isBoolean() ){
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        if( isSpatial( n[i], visited ) ){
          return true;
        }
      }
    }
  }
  return false;
}

RewriteResponse TheorySepRewriter::postRewrite(TNode node) {
  Trace("sep-postrewrite") << "Sep::postRewrite start " << node << std::endl;
  Node retNode = node;
  switch (node.getKind()) {
    case kind::SEP_STAR: {
      //flatten
      std::vector< Node > s_children;
      std::vector< Node > ns_children;
      getStarChildren( node, s_children, ns_children );
      if( !s_children.empty() ){
        Node schild;
        if( s_children.size()==1 ) {
          schild = s_children[0];
        }else{
          schild = NodeManager::currentNM()->mkNode( kind::SEP_STAR, s_children );
        }
        ns_children.push_back( schild );
      }
      Assert(!ns_children.empty());
      if( ns_children.size()==1 ){
        retNode = ns_children[0];
      }else{
        retNode = NodeManager::currentNM()->mkNode( kind::AND, ns_children );
      }
      break;
    }
    case kind::EQUAL: {
      if(node[0] == node[1]) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(true));
      }
      else if (node[0].isConst() && node[1].isConst()) {
        return RewriteResponse(REWRITE_DONE, NodeManager::currentNM()->mkConst(false));
      }
      if (node[0] > node[1]) {
        Node newNode = NodeManager::currentNM()->mkNode(node.getKind(), node[1], node[0]);
        return RewriteResponse(REWRITE_DONE, newNode);
      }
      break;
    }
    default:
      break;
  }
  if( node!=retNode ){
    Trace("sep-rewrite") << "Sep::rewrite : " << node << " -> " << retNode << std::endl;
  }
  return RewriteResponse(node==retNode ? REWRITE_DONE : REWRITE_AGAIN_FULL, retNode);
}

}  // namespace sep
}  // namespace theory
}  // namespace cvc5::internal

/*********************                                                        */
/*! \file theory_sep_rewriter.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/attribute.h"
#include "theory/sep/theory_sep_rewriter.h"
#include "theory/quantifiers/quant_util.h"
#include "options/sep_options.h"

namespace CVC4 {
namespace theory {
namespace sep {

void TheorySepRewriter::getStarChildren( Node n, std::vector< Node >& s_children, std::vector< Node >& ns_children ){
  Assert( n.getKind()==kind::SEP_STAR );
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
    case kind::SEP_LABEL: {
      if( node[0].getKind()==kind::SEP_PTO ){
        Node s = NodeManager::currentNM()->mkNode( kind::SINGLETON, node[0][0] );
        if( node[1]!=s ){
          Node c1 = node[1].eqNode( s );
          Node c2 = NodeManager::currentNM()->mkNode( kind::SEP_LABEL, NodeManager::currentNM()->mkNode( kind::SEP_PTO, node[0][0], node[0][1] ), s );
          retNode = NodeManager::currentNM()->mkNode( kind::AND, c1, c2 );
        }
      }
      if( node[0].getKind()==kind::SEP_EMP ){
        retNode = node[1].eqNode( NodeManager::currentNM()->mkConst(EmptySet(node[1].getType().toType())) );
      }
      break;
    }
    case kind::SEP_PTO: {
      break;
    }
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
      Assert( !ns_children.empty() );
      if( ns_children.size()==1 ){
        retNode = ns_children[0];
      }else{
        retNode = NodeManager::currentNM()->mkNode( kind::AND, ns_children );
      }
      break;
    }
    case kind::EQUAL:
    case kind::IFF: {
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

Node TheorySepRewriter::preSkolemEmp( Node n, bool pol, std::map< bool, std::map< Node, Node > >& visited ) {
  std::map< Node, Node >::iterator it = visited[pol].find( n );
  if( it==visited[pol].end() ){
    Trace("ajr-temp") << "Pre-skolem emp " << n << " with pol " << pol << std::endl;
    Node ret = n;
    if( n.getKind()==kind::SEP_EMP ){
      if( !pol ){
        TypeNode tnx = n[0].getType();
        TypeNode tny = n[1].getType();
        Node x = NodeManager::currentNM()->mkSkolem( "ex", tnx, "skolem location for negated emp" );
        Node y = NodeManager::currentNM()->mkSkolem( "ey", tny, "skolem data for negated emp" );
        return NodeManager::currentNM()->mkNode( kind::SEP_STAR, 
                 NodeManager::currentNM()->mkNode( kind::SEP_PTO, x, y ),
                 NodeManager::currentNM()->mkConst( true ) ).negate();
      }
    }else if( n.getKind()!=kind::FORALL && n.getNumChildren()>0 ){
      std::vector< Node > children;
      bool childChanged = false;
      if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
        children.push_back( n.getOperator() );
      }
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newPol, newHasPol;
        QuantPhaseReq::getPolarity( n, i, true, pol, newHasPol, newPol );
        Node nc = n[i];
        if( newHasPol ){
          nc = preSkolemEmp( n[i], newPol, visited );
          childChanged = childChanged || nc!=n[i];
        }
        children.push_back( nc );
      }
      if( childChanged ){
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
    visited[pol][n] = ret;
    return n;
  }else{
    return it->second;
  }
}

Node TheorySepRewriter::preprocess( Node n ) {
  if( options::sepPreSkolemEmp() ){
    bool pol = true;
    std::map< bool, std::map< Node, Node > > visited;
    n = preSkolemEmp( n, pol, visited );
  }
  return n;
}


}/* CVC4::theory::sep namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

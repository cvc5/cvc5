/*********************                                                        */
/*! \file theory_builtin_rewriter.cpp
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

#include "expr/attribute.h"
#include "theory/builtin/theory_builtin_rewriter.h"

#include "expr/chain.h"

using namespace std;

namespace CVC4 {
namespace theory {
namespace builtin {

Node TheoryBuiltinRewriter::blastDistinct(TNode in) {

  Assert(in.getKind() == kind::DISTINCT);

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 != pair will be generated so the
    // AND is not required
    Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, in[0], in[1]);
    Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
    return neq;
  }

  // assume that in.getNumChildren() > 2 => diseqs.size() > 1
  vector<Node> diseqs;
  for(TNode::iterator i = in.begin(); i != in.end(); ++i) {
    TNode::iterator j = i;
    while(++j != in.end()) {
      Node eq = NodeManager::currentNM()->mkNode(kind::EQUAL, *i, *j);
      Node neq = NodeManager::currentNM()->mkNode(kind::NOT, eq);
      diseqs.push_back(neq);
    }
  }
  Node out = NodeManager::currentNM()->mkNode(kind::AND, diseqs);
  return out;
}

Node TheoryBuiltinRewriter::blastChain(TNode in) {

  Assert(in.getKind() == kind::CHAIN);

  Kind chainedOp = in.getOperator().getConst<Chain>().getOperator();

  if(in.getNumChildren() == 2) {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return NodeManager::currentNM()->mkNode(chainedOp, in[0], in[1]);
  } else {
    NodeBuilder<> conj(kind::AND);
    for(TNode::iterator i = in.begin(), j = i + 1; j != in.end(); ++i, ++j) {
      conj << NodeManager::currentNM()->mkNode(chainedOp, *i, *j);
    }
    return conj;
  }
}

RewriteResponse TheoryBuiltinRewriter::postRewrite(TNode node) {
  if( node.getKind()==kind::LAMBDA ){
    Trace("builtin-rewrite") << "Rewriting lambda " << node << "..." << std::endl;
    Node anode = getArrayRepresentationForLambda( node );
    if( !anode.isNull() ){
      anode = Rewriter::rewrite( anode );
      Assert( anode.getType().isArray() );
      //must get the standard bound variable list
      Node varList = NodeManager::currentNM()->getBoundVarListForFunctionType( node.getType() );
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
  }
  else if (node.getKind() == kind::CHOICE)
  {
    if (node[1].getKind() == kind::EQUAL)
    {
      for (unsigned i = 0; i < 2; i++)
      {
        if (node[1][i] == node[0][0])
        {
          return RewriteResponse(REWRITE_DONE, node[1][1 - i]);
        }
      }
    }
    return RewriteResponse(REWRITE_DONE, node);
  }else{ 
    return doRewrite(node);
  }
}

TypeNode TheoryBuiltinRewriter::getFunctionTypeForArrayType(TypeNode atn,
                                                            Node bvl)
{
  std::vector<TypeNode> children;
  for (unsigned i = 0; i < bvl.getNumChildren(); i++)
  {
    Assert(atn.isArray());
    Assert(bvl[i].getType() == atn.getArrayIndexType());
    children.push_back(atn.getArrayIndexType());
    atn = atn.getArrayConstituentType();
  }
  children.push_back(atn);
  return NodeManager::currentNM()->mkFunctionType(children);
}

TypeNode TheoryBuiltinRewriter::getArrayTypeForFunctionType(TypeNode ftn)
{
  Assert(ftn.isFunction());
  // construct the curried array type
  unsigned nchildren = ftn.getNumChildren();
  TypeNode ret = ftn[nchildren - 1];
  for (int i = (static_cast<int>(nchildren) - 2); i >= 0; i--)
  {
    ret = NodeManager::currentNM()->mkArrayType(ftn[i], ret);
  }
  return ret;
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentationRec( TNode a, TNode bvl, unsigned bvlIndex, 
                                                                std::unordered_map< TNode, Node, TNodeHashFunction >& visited ){
  std::unordered_map< TNode, Node, TNodeHashFunction >::iterator it = visited.find( a );
  if( it==visited.end() ){
    Node ret;
    if( bvlIndex<bvl.getNumChildren() ){
      Assert( a.getType().isArray() );
      if( a.getKind()==kind::STORE ){
        // convert the array recursively
        Node body = getLambdaForArrayRepresentationRec( a[0], bvl, bvlIndex, visited );
        if( !body.isNull() ){
          // convert the value recursively (bounded by the number of arguments in bvl)
          Node val = getLambdaForArrayRepresentationRec( a[2], bvl, bvlIndex+1, visited );
          if( !val.isNull() ){
            Assert( !TypeNode::leastCommonTypeNode( a[1].getType(), bvl[bvlIndex].getType() ).isNull() );
            Assert( !TypeNode::leastCommonTypeNode( val.getType(), body.getType() ).isNull() );
            Node cond = bvl[bvlIndex].eqNode( a[1] );
            ret = NodeManager::currentNM()->mkNode( kind::ITE, cond, val, body );
          }
        }
      }else if( a.getKind()==kind::STORE_ALL ){
        ArrayStoreAll storeAll = a.getConst<ArrayStoreAll>();
        Node sa = Node::fromExpr(storeAll.getExpr());
        // convert the default value recursively (bounded by the number of arguments in bvl)
        ret = getLambdaForArrayRepresentationRec( sa, bvl, bvlIndex+1, visited );
      }
    }else{
      ret = a;
    }
    visited[a] = ret;
    return ret;
  }else{
    return it->second;
  }
}

Node TheoryBuiltinRewriter::getLambdaForArrayRepresentation( TNode a, TNode bvl ){
  Assert( a.getType().isArray() );
  std::unordered_map< TNode, Node, TNodeHashFunction > visited;
  Trace("builtin-rewrite-debug") << "Get lambda for : " << a << ", with variables " << bvl << std::endl;
  Node body = getLambdaForArrayRepresentationRec( a, bvl, 0, visited );
  if( !body.isNull() ){
    body = Rewriter::rewrite( body );
    Trace("builtin-rewrite-debug") << "...got lambda body " << body << std::endl;
    return NodeManager::currentNM()->mkNode( kind::LAMBDA, bvl, body );
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get lambda body" << std::endl;
    return Node::null();
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambdaRec( TNode n, bool reqConst, TypeNode retType ){
  Assert( n.getKind()==kind::LAMBDA );
  Trace("builtin-rewrite-debug") << "Get array representation for : " << n << std::endl;

  Node first_arg = n[0][0];
  Node rec_bvl;
  if( n[0].getNumChildren()>1 ){
    std::vector< Node > args;
    for( unsigned i=1; i<n[0].getNumChildren(); i++ ){
      args.push_back( n[0][i] );
    }
    rec_bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, args );
  }

  Trace("builtin-rewrite-debug2") << "  process body..." << std::endl;
  std::vector< Node > conds;
  std::vector< Node > vals;
  Node curr = n[1];
  while( curr.getKind()==kind::ITE || curr.getKind()==kind::EQUAL || curr.getKind()==kind::NOT ){
    Trace("builtin-rewrite-debug2") << "  process condition : " << curr[0] << std::endl;
    Node index_eq;
    Node curr_val;
    Node next;
    if( curr.getKind()==kind::ITE ){
      index_eq = curr[0];
      curr_val = curr[1];
      next = curr[2];
    }else{
      bool pol = curr.getKind()!=kind::NOT;
      //Boolean case, e.g. lambda x. (= x v) is lambda x. (ite (= x v) true false)
      index_eq = curr.getKind()==kind::NOT ? curr[0] : curr;
      curr_val = NodeManager::currentNM()->mkConst( pol );
      next = NodeManager::currentNM()->mkConst( !pol );
    }
    if( index_eq.getKind()!=kind::EQUAL ){
      // non-equality condition
      Trace("builtin-rewrite-debug2") << "  ...non-equality condition." << std::endl;
      return Node::null();
    }else if( reqConst && Rewriter::rewrite( index_eq )!=index_eq ){
      // equality must be oriented correctly based on rewriter
      Trace("builtin-rewrite-debug2") << "  ...equality not oriented properly." << std::endl;
      return Node::null();
    }

    Node curr_index;
    for( unsigned r=0; r<2; r++ ){
      Node arg = index_eq[r];
      Node val = index_eq[1-r];
      if( arg==first_arg ){
        if( reqConst && !val.isConst() ){
          // non-constant value
          Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
          return Node::null();
        }else{
          curr_index = val;
          Trace("builtin-rewrite-debug2") << "    " << arg << " -> " << val << std::endl;
          break;
        }
      }
    }
    if( !curr_index.isNull() ){
      if( !rec_bvl.isNull() ){
        curr_val = NodeManager::currentNM()->mkNode( kind::LAMBDA, rec_bvl, curr_val );
        curr_val = getArrayRepresentationForLambdaRec( curr_val, reqConst, retType );
        if( curr_val.isNull() ){
          Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
          return Node::null();
        }
      }      
      Trace("builtin-rewrite-debug2") << "  ...condition is index " << curr_val << std::endl;
    }else{
      Trace("builtin-rewrite-debug2") << "  ...non-constant value." << std::endl;
      return Node::null();
    }
    conds.push_back( curr_index );
    vals.push_back( curr_val );
    TypeNode vtype = curr_val.getType();
    //recurse
    curr = next;
  }
  if( !rec_bvl.isNull() ){
    curr = NodeManager::currentNM()->mkNode( kind::LAMBDA, rec_bvl, curr );
    curr = getArrayRepresentationForLambdaRec( curr, reqConst, retType );
  }
  if( !curr.isNull() && curr.isConst() ){
    // compute the return type
    TypeNode array_type = retType;
    for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
      unsigned index = (n[0].getNumChildren()-1)-i;
      array_type = NodeManager::currentNM()->mkArrayType( n[0][index].getType(), array_type );
    }
    Trace("builtin-rewrite-debug2") << "  make array store all " << curr.getType() << " annotated : " << array_type << std::endl;
    Assert( curr.getType().isSubtypeOf( array_type.getArrayConstituentType() ) );
    curr = NodeManager::currentNM()->mkConst(ArrayStoreAll(((ArrayType)array_type.toType()), curr.toExpr()));
    Trace("builtin-rewrite-debug2") << "  build array..." << std::endl;
    // can only build if default value is constant (since array store all must be constant)
    Trace("builtin-rewrite-debug2") << "  got constant base " << curr << std::endl;
    // construct store chain
    for( int i=((int)conds.size()-1); i>=0; i-- ){
      Assert( conds[i].getType().isSubtypeOf( first_arg.getType() ) );
      curr = NodeManager::currentNM()->mkNode( kind::STORE, curr, conds[i], vals[i] );
    }
    Trace("builtin-rewrite-debug") << "...got array " << curr << " for " << n << std::endl;
    return curr;
  }else{
    Trace("builtin-rewrite-debug") << "...failed to get array (cannot get constant default value)" << std::endl;
    return Node::null();    
  }
}

Node TheoryBuiltinRewriter::getArrayRepresentationForLambda( TNode n, bool reqConst ){
  Assert( n.getKind()==kind::LAMBDA );
  // must carry the overall return type to deal with cases like (lambda ((x Int)(y Int)) (ite (= x _) 0.5 0.0)),
  //  where the inner construction for the else case about should be (arraystoreall (Array Int Real) 0.0)
  return getArrayRepresentationForLambdaRec( n, reqConst, n[1].getType() );
}

}/* CVC4::theory::builtin namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

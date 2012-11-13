/*********************                                                        */
/*! \file quantifiers_rewriter.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of QuantifiersRewriter class
 **/

#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

bool QuantifiersRewriter::isClause( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isCube( n[0] );
  }else if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isClause( n[i] ) ){
        return false;
      }
    }
    return true;
  }else if( n.getKind()==IMPLIES ){
    return isCube( n[0] ) && isClause( n[1] );
  }else{
    return false;
  }
}

bool QuantifiersRewriter::isLiteral( Node n ){
  switch( n.getKind() ){
  case NOT:
    return isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
  case IFF:
    return false;
    break;
  case EQUAL:
    return n[0].getType()!=NodeManager::currentNM()->booleanType();
    break;
  default:
    break;
  }
  return true;
}

bool QuantifiersRewriter::isCube( Node n ){
  if( isLiteral( n ) ){
    return true;
  }else if( n.getKind()==NOT ){
    return isClause( n[0] );
  }else if( n.getKind()==AND ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !isCube( n[i] ) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void QuantifiersRewriter::addNodeToOrBuilder( Node n, NodeBuilder<>& t ){
  if( n.getKind()==OR ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      t << n[i];
    }
  }else{
    t << n;
  }
}

void QuantifiersRewriter::computeArgs( std::map< Node, bool >& active, Node n ){
  if( active.find( n )!=active.end() ){
    active[n] = true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgs( active, n[i] );
    }
  }
}

void QuantifiersRewriter::computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ){
  std::map< Node, bool > active;
  for( int i=0; i<(int)args.size(); i++ ){
    active[ args[i] ] = false;
  }
  //Notice() << "For " << n << " : " << std::endl;
  computeArgs( active, n );
  activeArgs.clear();
  for( std::map< Node, bool >::iterator it = active.begin(); it != active.end(); ++it ){
    Node n = it->first;
    //Notice() << "   " << it->first << " is " << it->second << std::endl;
    if( it->second ){ //only add bound variables that occur in body
      activeArgs.push_back( it->first );
    }
  }
}

bool QuantifiersRewriter::hasArg( std::vector< Node >& args, Node n ){
  if( std::find( args.begin(), args.end(), n )!=args.end() ){
    return true;
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( hasArg( args, n[i] ) ){
        return true;
      }
    }
    return false;
  }
}

void QuantifiersRewriter::setNestedQuantifiers( Node n, Node q ){
  if( n.getKind()==FORALL || n.getKind()==EXISTS ){
    Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
    NestedQuantAttribute nqai;
    n.setAttribute(nqai,q);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setNestedQuantifiers( n[i], q );
  }
}

RewriteResponse QuantifiersRewriter::preRewrite(TNode in) {
  Trace("quantifiers-rewrite-debug") << "pre-rewriting " << in << " " << in.hasAttribute(NestedQuantAttribute()) << std::endl;
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    if( !in.hasAttribute(NestedQuantAttribute()) ){
      setNestedQuantifiers( in[ 1 ], in );
    }
    std::vector< Node > args;
    for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
      args.push_back( in[0][i] );
    }
    Node body = in[1];
    bool doRewrite = false;
    while( body.getNumChildren()>=2 && body.getKind()==in.getKind() ){
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
      body = body[1];
      doRewrite = true;
    }
    if( doRewrite ){
      std::vector< Node > children;
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,args) );
      children.push_back( body );
      if( in.getNumChildren()==3 ){
        children.push_back( in[2] );
      }
      Node n = NodeManager::currentNM()->mkNode( in.getKind(), children );
      if( in!=n ){
        if( in.hasAttribute(NestedQuantAttribute()) ){
          setNestedQuantifiers( n, in.getAttribute(NestedQuantAttribute()) );
        }
        Trace("quantifiers-pre-rewrite") << "*** pre-rewrite " << in << std::endl;
        Trace("quantifiers-pre-rewrite") << " to " << std::endl;
        Trace("quantifiers-pre-rewrite") << n << std::endl;
      }
      return RewriteResponse(REWRITE_DONE, n);
    }
  }
  return RewriteResponse(REWRITE_DONE, in);
}

RewriteResponse QuantifiersRewriter::postRewrite(TNode in) {
  Trace("quantifiers-rewrite-debug") << "post-rewriting " << in << " " << in.hasAttribute(NestedQuantAttribute()) << std::endl;
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    RewriteStatus status = REWRITE_DONE;
    Node ret = in;
    //get the arguments
    std::vector< Node > args;
    for( int i=0; i<(int)in[0].getNumChildren(); i++ ){
      args.push_back( in[0][i] );
    }
    //get the instantiation pattern list
    Node ipl;
    if( in.getNumChildren()==3 ){
      ipl = in[2];
    }
    //get the body
    if( in.getKind()==EXISTS ){
      std::vector< Node > children;
      children.push_back( in[0] );
      children.push_back( in[1].negate() );
      if( in.getNumChildren()==3 ){
        children.push_back( in[2] );
      }
      ret = NodeManager::currentNM()->mkNode( FORALL, children );
      ret = ret.negate();
      status = REWRITE_AGAIN_FULL;
    }else{
      bool isNested = in.hasAttribute(NestedQuantAttribute());
      for( int op=0; op<COMPUTE_LAST; op++ ){
        if( doOperation( in, isNested, op ) ){
          ret = computeOperation( in, op );
          if( ret!=in ){
            status = REWRITE_AGAIN_FULL;
            break;
          }
        }
      }
    }
    //print if changed
    if( in!=ret ){
      if( in.hasAttribute(NestedQuantAttribute()) ){
        setNestedQuantifiers( ret, in.getAttribute(NestedQuantAttribute()) );
      }
      if( in.hasAttribute(InstConstantAttribute()) ){
        InstConstantAttribute ica;
        ret.setAttribute(ica,in.getAttribute(InstConstantAttribute()) );
      }
      Trace("quantifiers-rewrite") << "*** rewrite " << in << std::endl;
      Trace("quantifiers-rewrite") << " to " << std::endl;
      Trace("quantifiers-rewrite") << ret << std::endl;
    }
    return RewriteResponse( status, ret );
  }
  return RewriteResponse(REWRITE_DONE, in);
}

Node QuantifiersRewriter::computeNNF( Node body ){
  if( body.getKind()==NOT ){
    if( body[0].getKind()==NOT ){
      return computeNNF( body[0][0] );
    }else if( isLiteral( body[0] ) ){
      return body;
    }else{
      std::vector< Node > children;
      Kind k = body[0].getKind();
      if( body[0].getKind()==OR || body[0].getKind()==IMPLIES || body[0].getKind()==AND ){
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          Node nn = body[0].getKind()==IMPLIES && i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( computeNNF( nn ) );
        }
        k = body[0].getKind()==AND ? OR : AND;
      }else if( body[0].getKind()==XOR || body[0].getKind()==IFF ){
        for( int i=0; i<2; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( computeNNF( nn ) );
        }
      }else if( body[0].getKind()==ITE ){
        for( int i=0; i<3; i++ ){
          Node nn = i==0 ? body[0][i] : body[0][i].notNode();
          children.push_back( computeNNF( nn ) );
        }
      }else{
        Notice() << "Unhandled Quantifiers NNF: " << body << std::endl;
        return body;
      }
      return NodeManager::currentNM()->mkNode( k, children );
    }
  }else if( isLiteral( body ) ){
    return body;
  }else{
    std::vector< Node > children;
    bool childrenChanged = false;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      Node nc = computeNNF( body[i] );
      children.push_back( nc );
      childrenChanged = childrenChanged || nc!=body[i];
    }
    if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
}

Node QuantifiersRewriter::computeVarElimination( Node body, std::vector< Node >& args, Node& ipl ){
  Trace("var-elim-quant") << "Compute var elimination for " << body << std::endl;
  QuantPhaseReq qpr( body );
  std::vector< Node > vars;
  std::vector< Node > subs;
  for( std::map< Node, bool >::iterator it = qpr.d_phase_reqs.begin(); it != qpr.d_phase_reqs.end(); ++it ){
    //Notice() << "   " << it->first << " -> " << ( it->second ? "true" : "false" ) << std::endl;
    if( it->first.getKind()==EQUAL ){
      if( it->second ){
        for( int i=0; i<2; i++ ){
          int j = i==0 ? 1 : 0;
          std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), it->first[i] );
          if( ita!=args.end() ){
            std::vector< Node > temp;
            temp.push_back( it->first[i] );
            if( !hasArg( temp, it->first[j] ) ){
              vars.push_back( it->first[i] );
              subs.push_back( it->first[j] );
              args.erase( ita );
              break;
            }
          }
        }
        if( !vars.empty() ){
          break;
        }
      }
    }
  }
  if( !vars.empty() ){
    Trace("var-elim-quant") << "VE " << vars.size() << "/" << args.size() << std::endl;
    //remake with eliminated nodes
    body = body.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    body = Rewriter::rewrite( body );
    if( !ipl.isNull() ){
      ipl = ipl.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }
    Trace("var-elim-quant") << "Return " << body << std::endl;
  }
  return body;
}

Node QuantifiersRewriter::computeClause( Node n ){
  Assert( isClause( n ) );
  if( isLiteral( n ) ){
    return n;
  }else{
    NodeBuilder<> t(OR);
    if( n.getKind()==NOT ){
      if( n[0].getKind()==NOT ){
        return computeClause( n[0][0] );
      }else{
        //De-Morgan's law
        Assert( n[0].getKind()==AND );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          Node nn = computeClause( n[0][i].notNode() );
          addNodeToOrBuilder( nn, t );
        }
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        Node nc = ( ( i==0 && n.getKind()==IMPLIES ) ? n[i].notNode() : n[i] );
        Node nn = computeClause( nc );
        addNodeToOrBuilder( nn, t );
      }
    }
    return t.constructNode();
  }
}

Node QuantifiersRewriter::computeCNF( Node n, std::vector< Node >& args, NodeBuilder<>& defs, bool forcePred ){
  if( isLiteral( n ) ){
    return n;
  }else if( !forcePred && isClause( n ) ){
    return computeClause( n );
  }else{
    Kind k = ( n.getKind()==IMPLIES ? OR : ( n.getKind()==XOR ? IFF : n.getKind() ) );
    NodeBuilder<> t(k);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nc = ( i==0 && ( n.getKind()==IMPLIES || n.getKind()==XOR ) ) ? n[i].notNode() : n[i];
      Node ncnf = computeCNF( nc, args, defs, k!=OR );
      if( k==OR ){
        addNodeToOrBuilder( ncnf, t );
      }else{
        t << ncnf;
      }
    }
    if( !forcePred && k==OR ){
      return t.constructNode();
    }else{
      //compute the free variables
      Node nt = t;
      std::vector< Node > activeArgs;
      computeArgs( args, activeArgs, nt );
      std::vector< TypeNode > argTypes;
      for( int i=0; i<(int)activeArgs.size(); i++ ){
        argTypes.push_back( activeArgs[i].getType() );
      }
      //create the predicate
      Assert( argTypes.size()>0 );
      TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, NodeManager::currentNM()->booleanType() );
      std::stringstream ss;
      ss << "cnf_" << n.getKind() << "_" << n.getId();
      Node op = NodeManager::currentNM()->mkSkolem( ss.str(), typ, "was created by the quantifiers rewriter" );
      std::vector< Node > predArgs;
      predArgs.push_back( op );
      predArgs.insert( predArgs.end(), activeArgs.begin(), activeArgs.end() );
      Node pred = NodeManager::currentNM()->mkNode( APPLY_UF, predArgs );
      Trace("quantifiers-rewrite-cnf-debug") << "Made predicate " << pred << " for " << nt << std::endl;
      //create the bound var list
      Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, activeArgs );
      //now, look at the structure of nt
      if( nt.getKind()==NOT ){
        //case for NOT
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[0].notNode() : nt[0] );
          tt << ( i==0 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==OR ){
        //case for OR
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i].notNode() << pred;
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i];
        }
        tt << pred.notNode();
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==AND ){
        //case for AND
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          NodeBuilder<> tt(OR);
          tt << nt[i] << pred.notNode();
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
        NodeBuilder<> tt(OR);
        for( int i=0; i<(int)nt.getNumChildren(); i++ ){
          tt << nt[i].notNode();
        }
        tt << pred;
        defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
      }else if( nt.getKind()==IFF ){
        //case for IFF
        for( int i=0; i<4; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( ( i==0 || i==3 ) ? nt[0].notNode() : nt[0] );
          tt << ( ( i==1 || i==3 ) ? nt[1].notNode() : nt[1] );
          tt << ( ( i==0 || i==1 ) ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else if( nt.getKind()==ITE ){
        //case for ITE
        for( int j=1; j<=2; j++ ){
          for( int i=0; i<2; i++ ){
            NodeBuilder<> tt(OR);
            tt << ( ( j==1 ) ? nt[0].notNode() : nt[0] );
            tt << ( ( i==1 ) ? nt[j].notNode() : nt[j] );
            tt << ( ( i==0 ) ? pred.notNode() : pred );
            defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
          }
        }
        for( int i=0; i<2; i++ ){
          NodeBuilder<> tt(OR);
          tt << ( i==0 ? nt[1].notNode() : nt[1] );
          tt << ( i==0 ? nt[2].notNode() : nt[2] );
          tt << ( i==1 ? pred.notNode() : pred );
          defs << NodeManager::currentNM()->mkNode( FORALL, bvl, tt.constructNode() );
        }
      }else{
        Notice() << "Unhandled Quantifiers CNF: " << nt << std::endl;
      }
      return pred;
    }
  }
}

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args, bool pol, bool polReq ){
  if( body.getKind()==FORALL ){
    if( pol==polReq ){
      std::vector< Node > terms;
      std::vector< Node > subs;
      if( polReq ){
        //for doing prenexing of same-signed quantifiers
        //must rename each variable that already exists
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
          terms.push_back( body[0][i] );
          subs.push_back( NodeManager::currentNM()->mkBoundVar( body[0][i].getType() ) );
        }
        args.insert( args.end(), subs.begin(), subs.end() );
      }else{
        std::vector< TypeNode > argTypes;
        for( int i=0; i<(int)args.size(); i++ ){
          argTypes.push_back( args[i].getType() );
        }
        //for doing pre-skolemization of opposite-signed quantifiers
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          terms.push_back( body[0][i] );
          //make the new function symbol
          TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, body[0][i].getType() );
          Node op = NodeManager::currentNM()->mkSkolem( "op_$$", typ, "was created by the quantifiers rewriter" );
          std::vector< Node > funcArgs;
          funcArgs.push_back( op );
          funcArgs.insert( funcArgs.end(), args.begin(), args.end() );
          subs.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, funcArgs ) );
        }
      }
      Node newBody = body[1];
      newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
      Debug("quantifiers-substitute-debug") << "Did substitute have an effect" << (body[1] != newBody) << body[1] << " became " << newBody << endl;
      return newBody;
    }else{
      return body;
    }
  }else if( body.getKind()==ITE || body.getKind()==XOR || body.getKind()==IFF ){
    return body;
  }else{
    Assert( body.getKind()!=EXISTS );
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for( int i=0; i<(int)body.getNumChildren(); i++ ){
      bool newPol = ( body.getKind()==NOT || ( body.getKind()==IMPLIES && i==0 ) ) ? !pol : pol;
      Node n = computePrenex( body[i], args, newPol, polReq );
      newChildren.push_back( n );
      if( n!=body[i] ){
        childrenChanged = true;
      }
    }
    if( childrenChanged ){
      if( body.getKind()==NOT && newChildren[0].getKind()==NOT ){
        return newChildren[0][0];
      }else{
        return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
      }
    }else{
      return body;
    }
  }
}

//general method for computing various rewrites
Node QuantifiersRewriter::computeOperation( Node f, int computeOption ){
  if( f.getKind()==FORALL ){
    Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << std::endl;
    std::vector< Node > args;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      args.push_back( f[0][i] );
    }
    NodeBuilder<> defs(kind::AND);
    Node n = f[1];
    Node ipl;
    if( f.getNumChildren()==3 ){
      ipl = f[2];
    }
    if( computeOption==COMPUTE_MINISCOPING ){
      //return directly
      return computeMiniscoping( args, n, ipl, f.hasAttribute(NestedQuantAttribute()) );
    }else if( computeOption==COMPUTE_NNF ){
      n = computeNNF( n );
    }else if( computeOption==COMPUTE_PRENEX || computeOption==COMPUTE_PRE_SKOLEM ){
      n = computePrenex( n, args, true, computeOption==COMPUTE_PRENEX );
    }else if( computeOption==COMPUTE_VAR_ELIMINATION ){
      Node prev;
      do{
        prev = n;
        n = computeVarElimination( n, args, ipl );
      }while( prev!=n && !args.empty() );
    }else if( computeOption==COMPUTE_CNF ){
      //n = computeNNF( n );
      n = computeCNF( n, args, defs, false );
      ipl = Node::null();
    }
    Trace("quantifiers-rewrite-debug") << "Compute Operation: return " << n << ", " << args.size() << std::endl;
    if( f[1]==n && args.size()==f[0].getNumChildren() ){
      return f;
    }else{
      if( args.empty() ){
        defs << n;
      }else{
        std::vector< Node > children;
        children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
        children.push_back( n );
        if( !ipl.isNull() ){
          children.push_back( ipl );
        }
        defs << NodeManager::currentNM()->mkNode(kind::FORALL, children );
      }
      return defs.getNumChildren()==1 ? defs.getChild( 0 ) : defs.constructNode();
    }
  }else{
    return f;
  }
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node body, Node ipl ){
  std::vector< Node > activeArgs;
  computeArgs( args, activeArgs, body );
  if( activeArgs.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, activeArgs ) );
    children.push_back( body );
    if( !ipl.isNull() ){
      children.push_back( ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}

Node QuantifiersRewriter::computeMiniscoping( std::vector< Node >& args, Node body, Node ipl, bool isNested ){
  //Notice() << "rewrite quant " << body << std::endl;
  if( body.getKind()==FORALL ){
    //combine arguments
    std::vector< Node > newArgs;
    for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
      newArgs.push_back( body[0][i] );
    }
    newArgs.insert( newArgs.end(), args.begin(), args.end() );
    return mkForAll( newArgs, body[ 1 ], ipl );
  }else if( !isNested ){
    if( body.getKind()==NOT ){
      //push not downwards
      if( body[0].getKind()==NOT ){
        return computeMiniscoping( args, body[0][0], ipl );
      }else if( body[0].getKind()==AND ){
        if( doMiniscopingNoFreeVar() ){
          NodeBuilder<> t(kind::OR);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            t <<  ( body[0][i].getKind()==NOT ? body[0][i][0] : body[0][i].notNode() );
          }
          return computeMiniscoping( args, t.constructNode(), ipl );
        }
      }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
        if( doMiniscopingAnd() ){
          NodeBuilder<> t(kind::AND);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            Node trm = ( body[0].getKind()==IMPLIES && i==0 ) ? body[0][i] : ( body[0][i].getKind()==NOT  ? body[0][i][0] : body[0][i].notNode() );
            t << computeMiniscoping( args, trm, ipl );
          }
          return t.constructNode();
        }
      }
    }else if( body.getKind()==AND ){
      if( doMiniscopingAnd() ){
        //break apart
        NodeBuilder<> t(kind::AND);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          t << computeMiniscoping( args, body[i], ipl );
        }
        Node retVal = t;
        return retVal;
      }
    }else if( body.getKind()==OR || body.getKind()==IMPLIES ){
      if( doMiniscopingNoFreeVar() ){
        Node newBody = body;
        NodeBuilder<> body_split(kind::OR);
        NodeBuilder<> tb(kind::OR);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          Node trm = ( body.getKind()==IMPLIES && i==0 ) ? ( body[i].getKind()==NOT ? body[i][0] : body[i].notNode() ) : body[i];
          if( hasArg( args, body[i] ) ){
            tb << trm;
          }else{
            body_split << trm;
          }
        }
        if( tb.getNumChildren()==0 ){
          return body_split;
        }else if( body_split.getNumChildren()>0 ){
          newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
          body_split << mkForAll( args, newBody, ipl );
          return body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
        }
      }
    }
  }
  return mkForAll( args, body, ipl );
}
/*
Node QuantifiersRewriter::rewriteQuants( Node n, bool isNested ){
  if( n.getKind()==FORALL ){
    return rewriteQuant( n, isNested );
  }else if( isLiteral( n ) ){
    return n;
  }else{
    NodeBuilder<> tt(n.getKind());
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      tt << rewriteQuants( n[i], isNested );
    }
    return tt.constructNode();
  }
}

Node QuantifiersRewriter::rewriteQuant( Node n, bool isNested ){
  Node prev = n;
  for( int op=0; op<COMPUTE_LAST; op++ ){
    if( doOperation( n, isNested, op ) ){
      Node prev2 = n;
      n = computeOperation( n, op );
      if( prev2!=n ){
        Trace("quantifiers-rewrite-op") << "Rewrite op " << op << ": rewrite " << prev2 << std::endl;
        Trace("quantifiers-rewrite-op") << " to " << std::endl;
        Trace("quantifiers-rewrite-op") << n << std::endl;
      }
    }
  }
  if( prev==n ){
    return n;
  }else{
    //rewrite again until fix point is reached
    return rewriteQuant( n, isNested );
  }
}
*/

bool QuantifiersRewriter::doMiniscopingNoFreeVar(){
  return options::miniscopeQuantFreeVar();
}

bool QuantifiersRewriter::doMiniscopingAnd(){
  if( options::miniscopeQuant() ){
    return true;
  }else{
    if( options::cbqi() ){
      return true;
    }else{
      return false;
    }
  }
}

bool QuantifiersRewriter::doOperation( Node f, bool isNested, int computeOption ){
  if( computeOption==COMPUTE_MINISCOPING ){
    return true;
  }else if( computeOption==COMPUTE_NNF ){
    return false;//TODO: compute NNF (current bad idea since arithmetic rewrites equalities)
  }else if( computeOption==COMPUTE_PRE_SKOLEM ){
    return false;//options::preSkolemQuant();
  }else if( computeOption==COMPUTE_PRENEX ){
    return options::prenexQuant();
  }else if( computeOption==COMPUTE_VAR_ELIMINATION ){
    return options::varElimQuant();
  }else if( computeOption==COMPUTE_CNF ){
    return false;//return options::cnfQuant() ;
  }else{
    return false;
  }
}

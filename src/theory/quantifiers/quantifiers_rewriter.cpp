/*********************                                                        */
/*! \file quantifiers_rewriter.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

void QuantifiersRewriter::computeArgs( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ){
  if( n.getKind()==BOUND_VARIABLE ){
    if( std::find( args.begin(), args.end(), n )!=args.end() &&
        std::find( activeArgs.begin(), activeArgs.end(), n )==activeArgs.end() ){
      activeArgs.push_back( n );
    }
  }else{
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeArgs( args, activeArgs, n[i] );
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
  std::vector< Node > processed;
  setNestedQuantifiers2( n, q, processed );
}

void QuantifiersRewriter::setNestedQuantifiers2( Node n, Node q, std::vector< Node >& processed ) {
  if( std::find( processed.begin(), processed.end(), n )==processed.end() ){
    processed.push_back( n );
    if( n.getKind()==FORALL || n.getKind()==EXISTS ){
      Trace("quantifiers-rewrite-debug") << "Set nested quant attribute " << n << std::endl;
      NestedQuantAttribute nqai;
      n.setAttribute(nqai,q);
    }
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setNestedQuantifiers2( n[i], q, processed );
    }
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
      Trace("quantifiers-rewrite") << "*** rewrite " << in << std::endl;
      Trace("quantifiers-rewrite") << " to " << std::endl;
      Trace("quantifiers-rewrite") << ret << std::endl;
    }
    return RewriteResponse( status, ret );
  }
  return RewriteResponse(REWRITE_DONE, in);
}

Node QuantifiersRewriter::computeElimSymbols( Node body ) {
  if( isLiteral( body ) ){
    return body;
  }else{
    bool childrenChanged = false;
    std::vector< Node > children;
    for( unsigned i=0; i<body.getNumChildren(); i++ ){
      Node c = computeElimSymbols( body[i] );
      if( i==0 && ( body.getKind()==IMPLIES || body.getKind()==XOR ) ){
        c = c.negate();
      }
      children.push_back( c );
      childrenChanged = childrenChanged || c!=body[i];
    }
    if( body.getKind()==IMPLIES ){
      return NodeManager::currentNM()->mkNode( OR, children );
    }else if( body.getKind()==XOR ){
      return NodeManager::currentNM()->mkNode( IFF, children );
    }else if( childrenChanged ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }else{
      return body;
    }
  }
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
      if( body[0].getKind()==OR || body[0].getKind()==AND ){
        for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
          children.push_back( computeNNF( body[0][i].notNode() ) );
        }
        k = body[0].getKind()==AND ? OR : AND;
      }else if( body[0].getKind()==IFF ){
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

Node QuantifiersRewriter::computeSimpleIteLift( Node body ) {
  if( body.getKind()==EQUAL ){
    for( size_t i=0; i<2; i++ ){
      if( body[i].getKind()==ITE ){
        Node no = i==0 ? body[1] : body[0];
        bool doRewrite = false;
        std::vector< Node > children;
        children.push_back( body[i][0] );
        for( size_t j=1; j<=2; j++ ){
          //check if it rewrites to a constant
          Node nn = NodeManager::currentNM()->mkNode( EQUAL, no, body[i][j] );
          nn = Rewriter::rewrite( nn );
          children.push_back( nn );
          if( nn.isConst() ){
            doRewrite = true;
          }
        }
        if( doRewrite ){
          return NodeManager::currentNM()->mkNode( ITE, children );
        }
      }
    }
  }else if( body.getKind()!=APPLY_UF && body.getType()==NodeManager::currentNM()->booleanType() ){
    bool changed = false;
    std::vector< Node > children;
    for( size_t i=0; i<body.getNumChildren(); i++ ){
      Node nn = computeSimpleIteLift( body[i] );
      children.push_back( nn );
      changed = changed || nn!=body[i];
    }
    if( changed ){
      return NodeManager::currentNM()->mkNode( body.getKind(), children );
    }
  }
  return body;
}

Node QuantifiersRewriter::computeVarElimination( Node body, std::vector< Node >& args, Node& ipl ){
  Trace("var-elim-quant-debug") << "Compute var elimination for " << body << std::endl;
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
        Node nn = computeClause( n[i] );
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
    Kind k = n.getKind();
    NodeBuilder<> t(k);
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node nc = n[i];
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

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args, bool pol ){
  if( body.getKind()==FORALL ){
    if( pol ){
      std::vector< Node > terms;
      std::vector< Node > subs;
      //for doing prenexing of same-signed quantifiers
      //must rename each variable that already exists
      for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
        //if( std::find( args.begin(), args.end(), body[0][i] )!=args.end() ){
        terms.push_back( body[0][i] );
        subs.push_back( NodeManager::currentNM()->mkBoundVar( body[0][i].getType() ) );
      }
      args.insert( args.end(), subs.begin(), subs.end() );
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
      bool newPol = body.getKind()==NOT  ? !pol : pol;
      Node n = computePrenex( body[i], args, newPol );
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

Node QuantifiersRewriter::computeSplit( Node f, Node body, std::vector< Node >& vars ) {
  if( body.getKind()==OR ){
    size_t var_found_count = 0;
    size_t eqc_count = 0;
    size_t eqc_active = 0;
    std::map< Node, int > var_to_eqc;
    std::map< int, std::vector< Node > > eqc_to_var;
    std::map< int, std::vector< Node > > eqc_to_lit;

    std::vector<Node> lits;

    for( size_t i=0; i<body.getNumChildren(); i++ ){
      //get variables contained in the literal
      Node n = body[i];
      std::vector<Node> lit_vars;
      computeArgs( vars, lit_vars, n);
      //collectVars( n, vars, lit_vars );
      if (lit_vars.empty()) {
        lits.push_back(n);
      }else {
        std::vector<int> eqcs;
        std::vector<Node> lit_new_vars;
        //for each variable in literal
        for( size_t j=0; j<lit_vars.size(); j++) {
          //see if the variable has already been found
          if (var_to_eqc.find(lit_vars[j])!=var_to_eqc.end()) {
            int eqc = var_to_eqc[lit_vars[j]];
            if (std::find(eqcs.begin(), eqcs.end(), eqc)==eqcs.end()) {
              eqcs.push_back(eqc);
            }
          }
          else {
            var_found_count++;
            lit_new_vars.push_back(lit_vars[j]);
          }
        }
        if (eqcs.empty()) {
          eqcs.push_back(eqc_count);
          eqc_count++;
          eqc_active++;
        }

        int eqcz = eqcs[0];
        //merge equivalence classes with eqcz
        for (unsigned j=1; j<eqcs.size(); j++) {
          int eqc = eqcs[j];
          //move all variables from equivalence class
          for (unsigned k=0; k<eqc_to_var[eqc].size(); k++) {
            Node v = eqc_to_var[eqc][k];
            var_to_eqc[v] = eqcz;
            eqc_to_var[eqcz].push_back(v);
          }
          eqc_to_var.erase(eqc);
          //move all literals from equivalence class
          for (unsigned k=0; k<eqc_to_lit[eqc].size(); k++) {
            Node l = eqc_to_lit[eqc][k];
            eqc_to_lit[eqcz].push_back(l);
          }
          eqc_to_lit.erase(eqc);
          eqc_active--;
        }
        if (eqc_active==1 && var_found_count==vars.size()) {
          return f;
        }
        //add variables to equivalence class
        for (size_t j=0; j<lit_new_vars.size(); j++) {
          var_to_eqc[lit_new_vars[j]] = eqcz;
          eqc_to_var[eqcz].push_back(lit_new_vars[j]);
        }
        //add literal to equivalence class
        eqc_to_lit[eqcz].push_back(n);
      }
    }
    if (eqc_active>1) {
      Trace("clause-split-debug") << "Split clause " << f << std::endl;
      Trace("clause-split-debug") << "   Ground literals: " << std::endl;
      for( size_t i=0; i<lits.size(); i++) {
        Trace("clause-split-debug") << "      " << lits[i] << std::endl;
      }
      Trace("clause-split-debug") << std::endl;
      Trace("clause-split-debug") << "Equivalence classes: " << std::endl;
      for (std::map< int, std::vector< Node > >::iterator it = eqc_to_lit.begin(); it != eqc_to_lit.end(); ++it ){
        Trace("clause-split-debug") << "   Literals: " << std::endl;
        for (size_t i=0; i<it->second.size(); i++) {
          Trace("clause-split-debug") << "      " << it->second[i] << std::endl;
        }
        int eqc = it->first;
        Trace("clause-split-debug") << "   Variables: " << std::endl;
        for (size_t i=0; i<eqc_to_var[eqc].size(); i++) {
          Trace("clause-split-debug") << "      " << eqc_to_var[eqc][i] << std::endl;
        }
        Trace("clause-split-debug") << std::endl;
        Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, eqc_to_var[eqc]);
        Node body = it->second.size()==1 ? it->second[0] : NodeManager::currentNM()->mkNode(OR,it->second);
        Node fa = NodeManager::currentNM()->mkNode( FORALL, bvl, body );
        lits.push_back(fa);
      }
      Node nf = NodeManager::currentNM()->mkNode(OR,lits);
      Trace("clause-split-debug") << "Made node : " << nf << std::endl;
      return nf;
    }
  }
  return f;
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
    if( computeOption==COMPUTE_ELIM_SYMBOLS ){
      n = computeElimSymbols( n );
    }else if( computeOption==COMPUTE_MINISCOPING ){
      //return directly
      return computeMiniscoping( args, n, ipl, f.hasAttribute(NestedQuantAttribute()) );
    }else if( computeOption==COMPUTE_AGGRESSIVE_MINISCOPING ){
      return computeAggressiveMiniscoping( args, n, f.hasAttribute(NestedQuantAttribute()) );
    }else if( computeOption==COMPUTE_NNF ){
      n = computeNNF( n );
    }else if( computeOption==COMPUTE_SIMPLE_ITE_LIFT ){
      n = computeSimpleIteLift( n );
    }else if( computeOption==COMPUTE_PRENEX ){
      n = computePrenex( n, args, true );
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
    }else if( computeOption==COMPUTE_SPLIT ) {
      return computeSplit(f, n, args );
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
      }else if( body[0].getKind()==OR ){
        if( doMiniscopingAnd() ){
          NodeBuilder<> t(kind::AND);
          for( int i=0; i<(int)body[0].getNumChildren(); i++ ){
            Node trm = body[0][i].negate();
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
    }else if( body.getKind()==OR ){
      if( doMiniscopingNoFreeVar() ){
        Node newBody = body;
        NodeBuilder<> body_split(kind::OR);
        NodeBuilder<> tb(kind::OR);
        for( int i=0; i<(int)body.getNumChildren(); i++ ){
          Node trm = body[i];
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

Node QuantifiersRewriter::computeAggressiveMiniscoping( std::vector< Node >& args, Node body, bool isNested ){
  if( !isNested ){
    std::map< Node, std::vector< Node > > varLits;
    std::map< Node, std::vector< Node > > litVars;
    if( body.getKind()==OR ){
      Trace("ag-miniscope") << "compute aggressive miniscoping on " << body << std::endl;
      for( size_t i=0; i<body.getNumChildren(); i++ ){
        std::vector< Node > activeArgs;
        computeArgs( args, activeArgs, body[i] );
        for (unsigned j=0; j<activeArgs.size(); j++ ){
          varLits[activeArgs[j]].push_back( body[i] );
        }
        litVars[body[i]].insert( litVars[body[i]].begin(), activeArgs.begin(), activeArgs.end() );
      }
      //find the variable in the least number of literals
      Node bestVar;
      for( std::map< Node, std::vector< Node > >::iterator it = varLits.begin(); it != varLits.end(); ++it ){
        if( bestVar.isNull() || varLits[bestVar].size()>it->second.size() ){
          bestVar = it->first;
        }
      }
      Trace("ag-miniscope-debug") << "Best variable " << bestVar << " occurs in " << varLits[bestVar].size() << "/ " << body.getNumChildren() << " literals." << std::endl;
      if( !bestVar.isNull() && varLits[bestVar].size()<body.getNumChildren() ){
        //we can miniscope
        Trace("ag-miniscope") << "Miniscope on " << bestVar << std::endl;
        //make the bodies
        std::vector< Node > qlit1;
        qlit1.insert( qlit1.begin(), varLits[bestVar].begin(), varLits[bestVar].end() );
        std::vector< Node > qlitt;
        //for all literals not containing bestVar
        for( size_t i=0; i<body.getNumChildren(); i++ ){
          if( std::find( qlit1.begin(), qlit1.end(), body[i] )==qlit1.end() ){
            qlitt.push_back( body[i] );
          }
        }
        //make the variable lists
        std::vector< Node > qvl1;
        std::vector< Node > qvl2;
        std::vector< Node > qvsh;
        for( unsigned i=0; i<args.size(); i++ ){
          bool found1 = false;
          bool found2 = false;
          for( size_t j=0; j<varLits[args[i]].size(); j++ ){
            if( !found1 && std::find( qlit1.begin(), qlit1.end(), varLits[args[i]][j] )!=qlit1.end() ){
              found1 = true;
            }else if( !found2 && std::find( qlitt.begin(), qlitt.end(), varLits[args[i]][j] )!=qlitt.end() ){
              found2 = true;
            }
            if( found1 && found2 ){
              break;
            }
          }
          if( found1 ){
            if( found2 ){
              qvsh.push_back( args[i] );
            }else{
              qvl1.push_back( args[i] );
            }
          }else{
            Assert(found2);
            qvl2.push_back( args[i] );
          }
        }
        Assert( !qvl1.empty() );
        Assert( !qvl2.empty() || !qvsh.empty() );
        //check for literals that only contain shared variables
        std::vector< Node > qlitsh;
        std::vector< Node > qlit2;
        for( size_t i=0; i<qlitt.size(); i++ ){
          bool hasVar2 = false;
          for( size_t j=0; j<litVars[qlitt[i]].size(); j++ ){
            if( std::find( qvl2.begin(), qvl2.end(), litVars[qlitt[i]][j] )!=qvl2.end() ){
              hasVar2 = true;
              break;
            }
          }
          if( hasVar2 ){
            qlit2.push_back( qlitt[i] );
          }else{
            qlitsh.push_back( qlitt[i] );
          }
        }
        varLits.clear();
        litVars.clear();
        Trace("ag-miniscope-debug") << "Split into literals : " << qlit1.size() << " / " << qlit2.size() << " / " << qlitsh.size();
        Trace("ag-miniscope-debug") << ", variables : " << qvl1.size() << " / " << qvl2.size() << " / " << qvsh.size() << std::endl;
        Node n1 = qlit1.size()==1 ? qlit1[0] : NodeManager::currentNM()->mkNode( OR, qlit1 );
        n1 = computeAggressiveMiniscoping( qvl1, n1 );
        qlitsh.push_back( n1 );
        if( !qlit2.empty() ){
          Node n2 = qlit2.size()==1 ? qlit2[0] : NodeManager::currentNM()->mkNode( OR, qlit2 );
          n2 = computeAggressiveMiniscoping( qvl2, n2 );
          qlitsh.push_back( n2 );
        }
        Node n = NodeManager::currentNM()->mkNode( OR, qlitsh );
        if( !qvsh.empty() ){
          Node bvl = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, qvsh);
          n = NodeManager::currentNM()->mkNode( FORALL, bvl, n );
        }
        Trace("ag-miniscope") << "Return " << n << " for " << body << std::endl;
        return n;
      }
    }
  }
  return mkForAll( args, body, Node::null() );
}

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
  if( computeOption==COMPUTE_ELIM_SYMBOLS ){
    return true;
  }else if( computeOption==COMPUTE_MINISCOPING ){
    return true;
  }else if( computeOption==COMPUTE_AGGRESSIVE_MINISCOPING ){
    return options::aggressiveMiniscopeQuant();
  }else if( computeOption==COMPUTE_NNF ){
    return false;//TODO: compute NNF (current bad idea since arithmetic rewrites equalities)
  }else if( computeOption==COMPUTE_SIMPLE_ITE_LIFT ){
    return options::simpleIteLiftQuant();//!options::finiteModelFind();
  }else if( computeOption==COMPUTE_PRENEX ){
    return options::prenexQuant() && !options::aggressiveMiniscopeQuant();
  }else if( computeOption==COMPUTE_VAR_ELIMINATION ){
    return options::varElimQuant();
  }else if( computeOption==COMPUTE_CNF ){
    return false;//return options::cnfQuant() ;
  }else if( computeOption==COMPUTE_SPLIT ){
    return options::clauseSplit();
  }else{
    return false;
  }
}

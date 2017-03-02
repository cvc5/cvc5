/*********************                                                        */
/*! \file quantifiers_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of QuantifiersRewriter class
 **/

#include "theory/quantifiers/quantifiers_rewriter.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"

using namespace std;
using namespace CVC4::kind;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace quantifiers {

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
    return n[0].getKind()!=NOT && isLiteral( n[0] );
    break;
  case OR:
  case AND:
  case IMPLIES:
  case XOR:
  case ITE:
    return false;
    break;
  case EQUAL:
    //for boolean terms
    return !n[0].getType().isBoolean();
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

void QuantifiersRewriter::computeArgs( std::vector< Node >& args, std::map< Node, bool >& activeMap, Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    if( n.getKind()==BOUND_VARIABLE ){
      if( std::find( args.begin(), args.end(), n )!=args.end() ){
        activeMap[ n ] = true;
      }
    }else{
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        computeArgs( args, activeMap, n[i], visited );
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n ) {
  Assert( activeArgs.empty() );
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  if( !activeMap.empty() ){
    for( unsigned i=0; i<args.size(); i++ ){
      if( activeMap.find( args[i] )!=activeMap.end() ){
        activeArgs.push_back( args[i] );
      }
    }
  }
}

void QuantifiersRewriter::computeArgVec2( std::vector< Node >& args, std::vector< Node >& activeArgs, Node n, Node ipl ) {
  Assert( activeArgs.empty() );
  std::map< Node, bool > activeMap;
  std::map< Node, bool > visited;
  computeArgs( args, activeMap, n, visited );
  if( !activeMap.empty() ){
    //collect variables in inst pattern list only if we cannot eliminate quantifier
    computeArgs( args, activeMap, ipl, visited );
    for( unsigned i=0; i<args.size(); i++ ){
      if( activeMap.find( args[i] )!=activeMap.end() ){
        activeArgs.push_back( args[i] );
      }
    }
  }
}

RewriteResponse QuantifiersRewriter::preRewrite(TNode in) {
  if( in.getKind()==kind::EXISTS || in.getKind()==kind::FORALL ){
    Trace("quantifiers-rewrite-debug") << "pre-rewriting " << in << std::endl;
    std::vector< Node > args;
    Node body = in;
    bool doRewrite = false;
    while( body.getNumChildren()==2 && body.getKind()==body[1].getKind() ){
      for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }
      body = body[1];
      doRewrite = true;
    }
    if( doRewrite ){
      std::vector< Node > children;
      for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
        args.push_back( body[0][i] );
      }      
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST,args) );
      children.push_back( body[1] );
      if( body.getNumChildren()==3 ){
        children.push_back( body[2] );
      }
      Node n = NodeManager::currentNM()->mkNode( in.getKind(), children );
      if( in!=n ){
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
  Trace("quantifiers-rewrite-debug") << "post-rewriting " << in << std::endl;
  RewriteStatus status = REWRITE_DONE;
  Node ret = in;
  int rew_op = -1;
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
  }else if( in.getKind()==FORALL ){
    if( in[1].isConst() && in.getNumChildren()==2 ){
      return RewriteResponse( status, in[1] );
    }else{
      //compute attributes
      QAttributes qa;
      TermDb::computeQuantAttributes( in, qa );
      if( !qa.isRewriteRule() ){
        for( int op=0; op<COMPUTE_LAST; op++ ){
          if( doOperation( in, op, qa ) ){
            ret = computeOperation( in, op, qa );
            if( ret!=in ){
              rew_op = op;
              status = REWRITE_AGAIN_FULL;
              break;
            }
          }
        }
      }
    }
  }
  //print if changed
  if( in!=ret ){
    Trace("quantifiers-rewrite") << "*** rewrite (op=" << rew_op << ") " << in << std::endl;
    Trace("quantifiers-rewrite") << " to " << std::endl;
    Trace("quantifiers-rewrite") << ret << std::endl;
  }
  return RewriteResponse( status, ret );
}

bool QuantifiersRewriter::addCheckElimChild( std::vector< Node >& children, Node c, Kind k, std::map< Node, bool >& lit_pol, bool& childrenChanged ){
  if( ( k==OR || k==AND ) && options::elimTautQuant() ){
    Node lit = c.getKind()==NOT ? c[0] : c;
    bool pol = c.getKind()!=NOT;
    std::map< Node, bool >::iterator it = lit_pol.find( lit );
    if( it==lit_pol.end() ){
      lit_pol[lit] = pol;
      children.push_back( c );
    }else{
      childrenChanged = true;
      if( it->second!=pol ){
        return false;
      }
    }
  }else{
    children.push_back( c );
  }
  return true;
}

// eliminates IMPLIES/XOR, removes duplicates/infers tautologies of AND/OR, and computes NNF
Node QuantifiersRewriter::computeElimSymbols( Node body ) {
  Kind ok = body.getKind();
  Kind k = ok;
  bool negAllCh = false;
  bool negCh1 = false;
  if( ok==IMPLIES ){
    k = OR;
    negCh1 = true;
  }else if( ok==XOR ){
    k = EQUAL;
    negCh1 = true;
  }else if( ok==NOT ){
    if( body[0].getKind()==NOT ){
      return computeElimSymbols( body[0][0] );
    }else if( body[0].getKind()==OR || body[0].getKind()==IMPLIES ){
      k = AND;   
      negAllCh = true;
      negCh1 = body[0].getKind()==IMPLIES;
      body = body[0];
    }else if( body[0].getKind()==AND ){
      k = OR;
      negAllCh = true;
      body = body[0];
    }else if( body[0].getKind()==XOR || ( body[0].getKind()==EQUAL && body[0][0].getType().isBoolean() ) ){
      k = EQUAL;
      negCh1 = ( body[0].getKind()==EQUAL );
      body = body[0];
    }else if( body[0].getKind()==ITE ){
      k = body[0].getKind();
      negAllCh = true;
      negCh1 = true;
      body = body[0];
    }else{
      return body;
    }
  }else if( ( ok!=EQUAL || !body[0].getType().isBoolean() ) && ok!=ITE && ok!=AND && ok!=OR ){
    //a literal
    return body;
  }
  bool childrenChanged = false;
  std::vector< Node > children;
  std::map< Node, bool > lit_pol;
  for( unsigned i=0; i<body.getNumChildren(); i++ ){
    Node c = computeElimSymbols( ( i==0 && negCh1 )!=negAllCh ? body[i].negate() : body[i] );
    bool success = true;
    if( c.getKind()==k && ( k==OR || k==AND ) ){
      //flatten
      childrenChanged = true;
      for( unsigned j=0; j<c.getNumChildren(); j++ ){
        if( !addCheckElimChild( children, c[j], k, lit_pol, childrenChanged ) ){
          success = false;
          break;
        }
      }
    }else{
      success = addCheckElimChild( children, c, k, lit_pol, childrenChanged );
    }
    if( !success ){
      // tautology
      Assert( k==OR || k==AND );
      return NodeManager::currentNM()->mkConst( k==OR );
    }
    childrenChanged = childrenChanged || c!=body[i];
  }
  if( childrenChanged || k!=ok ){
    return ( children.size()==1 && k!=NOT ) ? children[0] : NodeManager::currentNM()->mkNode( k, children );
  }else{
    return body;
  }
}

void QuantifiersRewriter::computeDtTesterIteSplit( Node n, std::map< Node, Node >& pcons, std::map< Node, std::map< int, Node > >& ncons,
                                                   std::vector< Node >& conj ){
  if( n.getKind()==ITE && n[0].getKind()==APPLY_TESTER && n[1].getType().isBoolean() ){
    Trace("quantifiers-rewrite-ite-debug") << "Split tester condition : " << n << std::endl;
    Node x = n[0][0];
    std::map< Node, Node >::iterator itp = pcons.find( x );
    if( itp!=pcons.end() ){
      Trace("quantifiers-rewrite-ite-debug") << "...condition already set " << itp->second << std::endl;
      computeDtTesterIteSplit( n[ itp->second==n[0] ? 1 : 2 ], pcons, ncons, conj );
    }else{
      Expr testerExpr = n[0].getOperator().toExpr();
      int index = Datatype::indexOf( testerExpr );
      std::map< int, Node >::iterator itn = ncons[x].find( index );
      if( itn!=ncons[x].end() ){
        Trace("quantifiers-rewrite-ite-debug") << "...condition negated " << itn->second << std::endl;
        computeDtTesterIteSplit( n[ 2 ], pcons, ncons, conj );
      }else{
        for( unsigned i=0; i<2; i++ ){
          if( i==0 ){
            pcons[x] = n[0];
          }else{
            pcons.erase( x );
            ncons[x][index] = n[0].negate();
          }
          computeDtTesterIteSplit( n[i+1], pcons, ncons, conj );
        }
        ncons[x].erase( index );
      }
    }
  }else{
    Trace("quantifiers-rewrite-ite-debug") << "Return value : " << n << std::endl;
    std::vector< Node > children;
    children.push_back( n );
    std::vector< Node > vars;
    //add all positive testers
    for( std::map< Node, Node >::iterator it = pcons.begin(); it != pcons.end(); ++it ){
      children.push_back( it->second.negate() );
      vars.push_back( it->first );
    }
    //add all negative testers
    for( std::map< Node, std::map< int, Node > >::iterator it = ncons.begin(); it != ncons.end(); ++it ){
      Node x = it->first;
      //only if we haven't settled on a positive tester
      if( std::find( vars.begin(), vars.end(), x )==vars.end() ){
        //check if we have exhausted all options but one
        const Datatype& dt = DatatypeType(x.getType().toType()).getDatatype();
        std::vector< Node > nchildren;
        int pos_cons = -1;
        for( int i=0; i<(int)dt.getNumConstructors(); i++ ){
          std::map< int, Node >::iterator itt = it->second.find( i );
          if( itt==it->second.end() ){
            pos_cons = pos_cons==-1 ? i : -2;
          }else{
            nchildren.push_back( itt->second.negate() );
          }
        }
        if( pos_cons>=0 ){
          const DatatypeConstructor& c = dt[pos_cons];
          Expr tester = c.getTester();
          children.push_back( NodeManager::currentNM()->mkNode( kind::APPLY_TESTER, Node::fromExpr( tester ), x ).negate() );
        }else{
          children.insert( children.end(), nchildren.begin(), nchildren.end() );
        }
      }
    }
    //make condition/output pair
    Node c = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children );
    conj.push_back( c );
  }
}

int getEntailedCond( Node n, std::map< Node, bool >& currCond ){
  std::map< Node, bool >::iterator it = currCond.find( n );
  if( it!=currCond.end() ){
    return it->second ? 1 : -1;
  }else if( n.getKind()==NOT ){
    return -getEntailedCond( n[0], currCond );
  }else if( n.getKind()==AND || n.getKind()==OR ){
    bool hasZero = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      int res = getEntailedCond( n[i], currCond );
      if( res==0 ){
        hasZero = true;
      }else if( n.getKind()==AND && res==-1 ){
        return -1;
      }else if( n.getKind()==OR && res==1 ){
        return 1;
      }
    }
    return hasZero ? 0 : ( n.getKind()==AND ? 1 : -1 );
  }else if( n.getKind()==ITE ){
    int res = getEntailedCond( n[0], currCond );
    if( res==1 ){
      return getEntailedCond( n[1], currCond );
    }else if( res==-1 ){
      return getEntailedCond( n[2], currCond );
    }
  }else if( ( n.getKind()==EQUAL && n[0].getType().isBoolean() ) || n.getKind()==ITE ){
    unsigned start = n.getKind()==EQUAL ? 0 : 1;
    int res1 = 0;
    for( unsigned j=start; j<=(start+1); j++ ){
      int res = getEntailedCond( n[j], currCond );
      if( res==0 ){
        return 0;
      }else if( j==start ){
        res1 = res;
      }else{
        Assert( res!=0 );
        if( n.getKind()==ITE ){
          return res1==res ? res : 0;
        }else if( n.getKind()==EQUAL ){
          return res1==res ? 1 : -1;
        }
      }
    }
  }
  return 0;
}

bool addEntailedCond( Node n, bool pol, std::map< Node, bool >& currCond, std::vector< Node >& new_cond, bool& conflict ) {
  std::map< Node, bool >::iterator it = currCond.find( n );
  if( it==currCond.end() ){
    Trace("quantifiers-rewrite-term-debug") << "cond : " << n << " -> " << pol << std::endl;
    new_cond.push_back( n );
    currCond[n] = pol;
    return true;
  }else{
    if( it->second!=pol ){
      Trace("quantifiers-rewrite-term-debug") << "CONFLICTING cond : " << n << " -> " << pol << std::endl;
      conflict = true;
    }
    return false;
  }
}

void setEntailedCond( Node n, bool pol, std::map< Node, bool >& currCond, std::vector< Node >& new_cond, bool& conflict ) {
  if( ( n.getKind()==AND && pol ) || ( n.getKind()==OR && !pol ) ){
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setEntailedCond( n[i], pol, currCond, new_cond, conflict );
      if( conflict ){
        break;
      }
    }
  }else if( n.getKind()==NOT ){
    setEntailedCond( n[0], !pol, currCond, new_cond, conflict );
    return;
  }else if( n.getKind()==ITE ){
    int pol = getEntailedCond( n, currCond );
    if( pol==1 ){
      setEntailedCond( n[1], pol, currCond, new_cond, conflict );
    }else if( pol==-1 ){
      setEntailedCond( n[2], pol, currCond, new_cond, conflict );
    }
  }
  if( addEntailedCond( n, pol, currCond, new_cond, conflict ) ){
    if( n.getKind()==APPLY_TESTER ){
      const Datatype& dt = Datatype::datatypeOf(n.getOperator().toExpr());
      unsigned index = Datatype::indexOf(n.getOperator().toExpr());
      Assert( dt.getNumConstructors()>1 );
      if( pol ){
        for( unsigned i=0; i<dt.getNumConstructors(); i++ ){
          if( i!=index ){
            Node t = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[i].getTester() ), n[0] );
            addEntailedCond( t, false, currCond, new_cond, conflict );
          }
        }
      }else{
        if( dt.getNumConstructors()==2 ){
          int oindex = 1-index;
          Node t = NodeManager::currentNM()->mkNode( APPLY_TESTER, Node::fromExpr( dt[oindex].getTester() ), n[0] );
          addEntailedCond( t, true, currCond, new_cond, conflict );
        }
      }
    }
  }
}

void removeEntailedCond( std::map< Node, bool >& currCond, std::vector< Node >& new_cond, std::map< Node, Node >& cache ) {
  if( !new_cond.empty() ){
    for( unsigned j=0; j<new_cond.size(); j++ ){
      currCond.erase( new_cond[j] );
    }
    new_cond.clear();
    cache.clear();
  }
}

Node QuantifiersRewriter::computeProcessTerms( Node body, std::vector< Node >& new_vars, std::vector< Node >& new_conds, Node q, QAttributes& qa ){
  std::map< Node, bool > curr_cond;
  std::map< Node, Node > cache;
  std::map< Node, Node > icache;
  if( qa.isFunDef() ){
    Node h = TermDb::getFunDefHead( q );
    Assert( !h.isNull() );
    // if it is a function definition, rewrite the body independently
    Node fbody = TermDb::getFunDefBody( q );
    Assert( !body.isNull() );
    Trace("quantifiers-rewrite-debug") << "Decompose " << h << " / " << fbody << " as function definition for " << q << "." << std::endl;
    Node r = computeProcessTerms2( fbody, true, true, curr_cond, 0, cache, icache, new_vars, new_conds );
    return Rewriter::rewrite( NodeManager::currentNM()->mkNode( EQUAL, h, r ) );
  }else{
    return computeProcessTerms2( body, true, true, curr_cond, 0, cache, icache, new_vars, new_conds );
  }
}

Node QuantifiersRewriter::computeProcessTerms2( Node body, bool hasPol, bool pol, std::map< Node, bool >& currCond, int nCurrCond,
                                                std::map< Node, Node >& cache, std::map< Node, Node >& icache,
                                                std::vector< Node >& new_vars, std::vector< Node >& new_conds ) {
  Trace("quantifiers-rewrite-term-debug2") << "computeProcessTerms " << body << " " << hasPol << " " << pol << std::endl;
  Node ret;
  std::map< Node, Node >::iterator iti = cache.find( body );
  if( iti!=cache.end() ){
    ret = iti->second;
    Trace("quantifiers-rewrite-term-debug2") << "Return (cached) " << ret << " for " << body << std::endl;
  }else{
    //only do context dependent processing up to depth 8
    bool doCD = nCurrCond<8;
    bool changed = false;
    std::vector< Node > children;
    //set entailed conditions based on OR/AND
    std::map< int, std::vector< Node > > new_cond_children;
    if( doCD && ( body.getKind()==OR || body.getKind()==AND ) ){
      nCurrCond = nCurrCond + 1;
      bool conflict = false;
      bool use_pol = body.getKind()==AND;
      for( unsigned j=0; j<body.getNumChildren(); j++ ){
        setEntailedCond( body[j], use_pol, currCond, new_cond_children[j], conflict );
      }
      if( conflict ){
        Trace("quantifiers-rewrite-term-debug") << "-------conflict, return " << !use_pol << std::endl;
        ret = NodeManager::currentNM()->mkConst( !use_pol );
      }
    }
    if( ret.isNull() ){
      for( size_t i=0; i<body.getNumChildren(); i++ ){
      
        //set/update entailed conditions
        std::vector< Node > new_cond;
        bool conflict = false;
        if( doCD ){
          if( Trace.isOn("quantifiers-rewrite-term-debug") ){
            if( ( body.getKind()==ITE && i>0 ) || body.getKind()==OR || body.getKind()==AND ){
              Trace("quantifiers-rewrite-term-debug") << "---rewrite " << body[i] << " under conditions:----" << std::endl;
            }
          }
          if( body.getKind()==ITE && i>0 ){
            if( i==1 ){
              nCurrCond = nCurrCond + 1;
            }
            setEntailedCond( children[0], i==1, currCond, new_cond, conflict );
            //should not conflict (entailment check failed) 
            Assert( !conflict );
          }
          if( body.getKind()==OR || body.getKind()==AND ){
            bool use_pol = body.getKind()==AND;
            //remove the current condition
            removeEntailedCond( currCond, new_cond_children[i], cache );
            if( i>0 ){
              //add the previous condition
              setEntailedCond( children[i-1], use_pol, currCond, new_cond_children[i-1], conflict );
            }
            if( conflict ){
              Trace("quantifiers-rewrite-term-debug") << "-------conflict, return " << !use_pol << std::endl;
              ret = NodeManager::currentNM()->mkConst( !use_pol );
            }
          }
          if( !new_cond.empty() ){
            cache.clear();
          }
          if( Trace.isOn("quantifiers-rewrite-term-debug") ){
            if( ( body.getKind()==ITE && i>0 ) || body.getKind()==OR || body.getKind()==AND ){      
              Trace("quantifiers-rewrite-term-debug") << "-------" << std::endl;
            }
          }
        }
        
        //do the recursive call on children
        if( !conflict ){
          bool newHasPol;
          bool newPol;
          QuantPhaseReq::getPolarity( body, i, hasPol, pol, newHasPol, newPol );
          Node nn = computeProcessTerms2( body[i], newHasPol, newPol, currCond, nCurrCond, cache, icache, new_vars, new_conds );
          if( body.getKind()==ITE && i==0 ){
            int res = getEntailedCond( nn, currCond );
            Trace("quantifiers-rewrite-term-debug") << "Condition for " << body << " is " << nn << ", entailment check=" << res << std::endl;
            if( res==1 ){
              ret = computeProcessTerms2( body[1], hasPol, pol, currCond, nCurrCond, cache, icache, new_vars, new_conds );
            }else if( res==-1 ){
              ret = computeProcessTerms2( body[2], hasPol, pol, currCond, nCurrCond, cache, icache, new_vars, new_conds );
            }
          }
          children.push_back( nn );
          changed = changed || nn!=body[i];
        }
        
        //clean up entailed conditions
        removeEntailedCond( currCond, new_cond, cache );
        
        if( !ret.isNull() ){
          break;
        }
      }
      
      //make return value
      if( ret.isNull() ){
        if( changed ){
          if( body.getMetaKind() == kind::metakind::PARAMETERIZED ){
            children.insert( children.begin(), body.getOperator() );
          }
          ret = NodeManager::currentNM()->mkNode( body.getKind(), children );
        }else{
          ret = body;
        }
      }
    }
    
    //clean up entailed conditions
    if( body.getKind()==OR || body.getKind()==AND ){
      for( unsigned j=0; j<body.getNumChildren(); j++ ){
        removeEntailedCond( currCond, new_cond_children[j], cache );
      }
    }
    
    Trace("quantifiers-rewrite-term-debug2") << "Returning " << ret << " for " << body << std::endl;
    cache[body] = ret;
  }

  //do context-independent rewriting
  iti = icache.find( ret );
  if( iti!=icache.end() ){
    return iti->second;
  }else{
    Node prev = ret;
    if( ret.getKind()==EQUAL && options::iteLiftQuant()!=ITE_LIFT_QUANT_MODE_NONE ){
      for( size_t i=0; i<2; i++ ){
        if( ret[i].getKind()==ITE ){
          Node no = i==0 ? ret[1] : ret[0];
          if( no.getKind()!=ITE ){
            bool doRewrite = options::iteLiftQuant()==ITE_LIFT_QUANT_MODE_ALL;
            std::vector< Node > children;
            children.push_back( ret[i][0] );
            for( size_t j=1; j<=2; j++ ){
              //check if it rewrites to a constant
              Node nn = NodeManager::currentNM()->mkNode( EQUAL, no, ret[i][j] );
              nn = Rewriter::rewrite( nn );
              children.push_back( nn );
              if( nn.isConst() ){
                doRewrite = true;
              }
            }
            if( doRewrite ){
              ret = NodeManager::currentNM()->mkNode( ITE, children );
              break;
            }
          }
        }
      }
    /* ITE lifting
    if( ret.getKind()==ITE ){
      TypeNode ite_t = ret[1].getType();
      if( !ite_t.isBoolean() ){
        ite_t = TypeNode::leastCommonTypeNode( ite_t, ret[2].getType() );
        Node ite_v = NodeManager::currentNM()->mkBoundVar(ite_t);
        new_vars.push_back( ite_v );
        Node cond = NodeManager::currentNM()->mkNode(kind::ITE, ret[0], ite_v.eqNode( ret[1] ), ite_v.eqNode( ret[2] ) );
        new_conds.push_back( cond.negate() );
        ret = ite_v;
      }
      */
    }else if( options::elimExtArithQuant() ){
      if( ret.getKind()==INTS_DIVISION_TOTAL || ret.getKind()==INTS_MODULUS_TOTAL ){
        Node num = ret[0];
        Node den = ret[1];
        if(den.isConst()) {
          const Rational& rat = den.getConst<Rational>();
          Assert(!num.isConst());
          if(rat != 0) {
            Node intVar = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
            new_vars.push_back( intVar );
            Node cond;
            if(rat > 0) {
              cond = NodeManager::currentNM()->mkNode(kind::AND,
                       NodeManager::currentNM()->mkNode(kind::LEQ, NodeManager::currentNM()->mkNode(kind::MULT, den, intVar), num),
                       NodeManager::currentNM()->mkNode(kind::LT, num,
                         NodeManager::currentNM()->mkNode(kind::MULT, den, NodeManager::currentNM()->mkNode(kind::PLUS, intVar, NodeManager::currentNM()->mkConst(Rational(1))))));
            } else {
              cond = NodeManager::currentNM()->mkNode(kind::AND,
                       NodeManager::currentNM()->mkNode(kind::LEQ, NodeManager::currentNM()->mkNode(kind::MULT, den, intVar), num),
                       NodeManager::currentNM()->mkNode(kind::LT, num,
                         NodeManager::currentNM()->mkNode(kind::MULT, den, NodeManager::currentNM()->mkNode(kind::PLUS, intVar, NodeManager::currentNM()->mkConst(Rational(-1))))));
            }
            new_conds.push_back( cond.negate() );
            if( ret.getKind()==INTS_DIVISION_TOTAL ){
              ret = intVar;
            }else{
              ret = NodeManager::currentNM()->mkNode(kind::MINUS, num, NodeManager::currentNM()->mkNode(kind::MULT, den, intVar));
            }
          }
        }
      }else if( ret.getKind()==TO_INTEGER || ret.getKind()==IS_INTEGER ){
        Node intVar = NodeManager::currentNM()->mkBoundVar(NodeManager::currentNM()->integerType());
        new_vars.push_back( intVar );
        new_conds.push_back(NodeManager::currentNM()->mkNode(kind::AND,
                              NodeManager::currentNM()->mkNode(kind::LT,
                                NodeManager::currentNM()->mkNode(kind::MINUS, ret[0], NodeManager::currentNM()->mkConst(Rational(1))), intVar),
                              NodeManager::currentNM()->mkNode(kind::LEQ, intVar, ret[0])).negate());
        if( ret.getKind()==TO_INTEGER ){
          ret = intVar;
        }else{
          ret = ret[0].eqNode( intVar );
        }
      }
    }
    icache[prev] = ret;
    return ret;
  }
}


bool QuantifiersRewriter::isConditionalVariableElim( Node n, int pol ){
  if( n.getKind()==NOT ){
    return isConditionalVariableElim( n[0], -pol );
  }else if( ( n.getKind()==AND && pol>=0 ) || ( n.getKind()==OR && pol<=0 ) ){
    pol = n.getKind()==AND ? 1 : -1;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      if( isConditionalVariableElim( n[i], pol ) ){
        return true;
      }
    }
  }else if( n.getKind()==EQUAL ){
    for( unsigned i=0; i<2; i++ ){
      if( n[i].getKind()==BOUND_VARIABLE ){
        if( !TermDb::containsTerm( n[1-i], n[i] ) ){
          return true;
        }
      }
    }
  }else if( n.getKind()==BOUND_VARIABLE ){
    return true;
  }
  return false;
}

Node QuantifiersRewriter::computeCondSplit( Node body, QAttributes& qa ){
  if( options::iteDtTesterSplitQuant() && body.getKind()==ITE ){
    Trace("quantifiers-rewrite-ite-debug") << "DTT split : " << body << std::endl;
    std::map< Node, Node > pcons;
    std::map< Node, std::map< int, Node > > ncons;
    std::vector< Node > conj;
    computeDtTesterIteSplit( body, pcons, ncons, conj );
    Assert( !conj.empty() );
    if( conj.size()>1 ){
      Trace("quantifiers-rewrite-ite") << "*** Split ITE (datatype tester) " << body << " into : " << std::endl;
      for( unsigned i=0; i<conj.size(); i++ ){
        Trace("quantifiers-rewrite-ite") << "   " << conj[i] << std::endl;
      }
      return NodeManager::currentNM()->mkNode( AND, conj );
    }
  }
  if( options::condVarSplitQuant() ){
    if( body.getKind()==ITE || ( body.getKind()==EQUAL && body[0].getType().isBoolean() && options::condVarSplitQuantAgg() ) ){
      Assert( !qa.isFunDef() );
      Trace("quantifiers-rewrite-debug") << "Conditional var elim split " << body << "?" << std::endl;
      bool do_split = false;
      unsigned index_max = body.getKind()==ITE ? 0 : 1;
      for( unsigned index=0; index<=index_max; index++ ){
        if( isConditionalVariableElim( body[index] ) ){
          do_split = true;
          break;
        }
      }
      if( do_split ){
        Node pos;
        Node neg;
        if( body.getKind()==ITE ){
          pos = NodeManager::currentNM()->mkNode( OR, body[0].negate(), body[1] );
          neg = NodeManager::currentNM()->mkNode( OR, body[0], body[2] );
        }else{
          pos = NodeManager::currentNM()->mkNode( OR, body[0].negate(), body[1] );
          neg = NodeManager::currentNM()->mkNode( OR, body[0], body[1].negate() );
        }
        Trace("quantifiers-rewrite-debug") << "*** Split (conditional variable eq) " << body << " into : " << std::endl;
        Trace("quantifiers-rewrite-debug") << "   " << pos << std::endl;
        Trace("quantifiers-rewrite-debug") << "   " << neg << std::endl;
        return NodeManager::currentNM()->mkNode( AND, pos, neg );
      }
    }else if( body.getKind()==OR && options::condVarSplitQuantAgg() ){
      std::vector< Node > bchildren;
      std::vector< Node > nchildren;
      for( unsigned i=0; i<body.getNumChildren(); i++ ){
        bool split = false;
        if( nchildren.empty() ){
          if( body[i].getKind()==AND ){
            std::vector< Node > children;
            for( unsigned j=0; j<body[i].getNumChildren(); j++ ){
              if( ( body[i][j].getKind()==NOT && body[i][j][0].getKind()==EQUAL && isConditionalVariableElim( body[i][j][0] ) ) ||
                  body[i][j].getKind()==BOUND_VARIABLE ){
                nchildren.push_back( body[i][j] );
              }else{
                children.push_back( body[i][j] );
              }
            }
            if( !nchildren.empty() ){
              if( !children.empty() ){
                nchildren.push_back( children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( AND, children ) );
              }
              split = true;
            }
          }
        }
        if( !split ){
          bchildren.push_back( body[i] );
        }
      }
      if( !nchildren.empty() ){
        Trace("quantifiers-rewrite-debug") << "*** Split (conditional variable eq) " << body << " into : " << std::endl;
        for( unsigned i=0; i<nchildren.size(); i++ ){
          bchildren.push_back( nchildren[i] );
          nchildren[i] = NodeManager::currentNM()->mkNode( OR, bchildren );
          Trace("quantifiers-rewrite-debug") << "   " << nchildren[i] << std::endl;
          bchildren.pop_back();
        }
        return NodeManager::currentNM()->mkNode( AND, nchildren );
      }
    }
  }
  return body;
}

bool QuantifiersRewriter::isVariableElim( Node v, Node s ) {
  if( TermDb::containsTerm( s, v ) || !s.getType().isSubtypeOf( v.getType() ) ){
    return false;
  }else{
    return true;
  }
}

void QuantifiersRewriter::isVariableBoundElig( Node n, std::map< Node, int >& exclude, std::map< Node, std::map< int, bool > >& visited, bool hasPol, bool pol, 
                                               std::map< Node, bool >& elig_vars  ) {
  int vindex = hasPol ? ( pol ? 1 : -1 ) : 0;
  if( visited[n].find( vindex )==visited[n].end() ){
    visited[n][vindex] = true;
    if( elig_vars.find( n )!=elig_vars.end() ){
      //variable contained in a place apart from bounds, no longer eligible for elimination
      elig_vars.erase( n );
      Trace("var-elim-ineq-debug") << "...found occurrence of " << n << ", mark ineligible" << std::endl;
    }else{
      if( hasPol ){
        std::map< Node, int >::iterator itx = exclude.find( n );
        if( itx!=exclude.end() && itx->second==vindex ){
          //already processed this literal
          return;
        }
      }
      for( unsigned j=0; j<n.getNumChildren(); j++ ){
        bool newHasPol;
        bool newPol;
        QuantPhaseReq::getPolarity( n, j, hasPol, pol, newHasPol, newPol );
        isVariableBoundElig( n[j], exclude, visited, newHasPol, newPol, elig_vars );
        if( elig_vars.empty() ){
          break;
        }
      }
    }
  }else{
    //already visited
  }
}

bool QuantifiersRewriter::computeVariableElimLit( Node lit, bool pol, std::vector< Node >& args, std::vector< Node >& vars, std::vector< Node >& subs,
                                                  std::map< Node, std::map< bool, std::map< Node, bool > > >& num_bounds ) {
  if( lit.getKind()==EQUAL && pol && options::varElimQuant() ){
    for( unsigned i=0; i<2; i++ ){
      std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), lit[i] );
      if( ita!=args.end() ){
        if( isVariableElim( lit[i], lit[1-i] ) ){
          Trace("var-elim-quant") << "Variable eliminate based on equality : " << lit[i] << " -> " << lit[1-i] << std::endl;
          vars.push_back( lit[i] );
          subs.push_back( lit[1-i] );
          args.erase( ita );
          return true;
        }
      }
    }
  }else if( lit.getKind()==APPLY_TESTER && pol && lit[0].getKind()==BOUND_VARIABLE && options::dtVarExpandQuant() ){
    Trace("var-elim-dt") << "Expand datatype variable based on : " << lit << std::endl;
    std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), lit[0] );
    if( ita!=args.end() ){
      vars.push_back( lit[0] );
      Expr testerExpr = lit.getOperator().toExpr();
      int index = Datatype::indexOf( testerExpr );
      const Datatype& dt = Datatype::datatypeOf(testerExpr);
      const DatatypeConstructor& c = dt[index];
      std::vector< Node > newChildren;
      newChildren.push_back( Node::fromExpr( c.getConstructor() ) );
      std::vector< Node > newVars;
      for( unsigned j=0; j<c.getNumArgs(); j++ ){
        TypeNode tn = TypeNode::fromType( c[j].getRangeType() );
        Node v = NodeManager::currentNM()->mkBoundVar( tn );
        newChildren.push_back( v );
        newVars.push_back( v );
      }
      subs.push_back( NodeManager::currentNM()->mkNode( APPLY_CONSTRUCTOR, newChildren ) );
      Trace("var-elim-dt") << "...apply substitution " << subs[0] << "/" << vars[0] << std::endl;
      args.erase( ita );
      args.insert( args.end(), newVars.begin(), newVars.end() );
      return true;
    }
  }else if( lit.getKind()==BOUND_VARIABLE && options::varElimQuant() ){
    std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), lit );
    if( ita!=args.end() ){
      Trace("var-elim-bool") << "Variable eliminate : " << lit << std::endl;
      vars.push_back( lit );
      subs.push_back( NodeManager::currentNM()->mkConst( pol ) );
      args.erase( ita );
      return true;
    }
  }
  if( ( lit.getKind()==EQUAL && lit[0].getType().isReal() && pol ) || ( ( lit.getKind()==GEQ || lit.getKind()==GT ) && options::varIneqElimQuant() ) ){
    //for arithmetic, solve the (in)equality
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSumLit( lit, msum ) ){
      for( std::map< Node, Node >::iterator itm = msum.begin(); itm != msum.end(); ++itm ){
        if( !itm->first.isNull() ){
          std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), itm->first );
          if( ita!=args.end() ){
            if( lit.getKind()==EQUAL ){
              Assert( pol );
              Node veq_c;
              Node val;
              int ires = QuantArith::isolate( itm->first, msum, veq_c, val, EQUAL );
              if( ires!=0 && veq_c.isNull() && isVariableElim( itm->first, val ) ){
                Trace("var-elim-quant") << "Variable eliminate based on solved equality : " << itm->first << " -> " << val << std::endl;
                vars.push_back( itm->first );
                subs.push_back( val );
                args.erase( ita );
                return true;
              }
            }else{
              Assert( lit.getKind()==GEQ || lit.getKind()==GT );
              //store that this literal is upper/lower bound for itm->first
              Node veq_c;
              Node val;
              int ires = QuantArith::isolate( itm->first, msum, veq_c, val, lit.getKind() );
              if( ires!=0 && veq_c.isNull() ){
                bool is_upper = pol!=( ires==1 );
                Trace("var-elim-ineq-debug") << lit << " is a " << ( is_upper ? "upper" : "lower" ) << " bound for " << itm->first << std::endl;
                Trace("var-elim-ineq-debug") << "  pol/ires = " << pol << " " << ires << std::endl;
                num_bounds[itm->first][is_upper][lit] = pol;
              }else{
                Trace("var-elim-ineq-debug") << "...ineligible " << itm->first << " since it cannot be solved for (" << ires << ", " << veq_c << ")." << std::endl;
                num_bounds[itm->first][true].clear();
                num_bounds[itm->first][false].clear();
              }
            }
          }else{
            if( lit.getKind()==GEQ || lit.getKind()==GT ){
              //compute variables in itm->first, these are not eligible for elimination
              std::vector< Node > bvs;
              TermDb::getBoundVars( itm->first, bvs );
              for( unsigned j=0; j<bvs.size(); j++ ){
                Trace("var-elim-ineq-debug") << "...ineligible " << bvs[j] << " since it is contained in monomial." << std::endl;
                num_bounds[bvs[j]][true].clear();
                num_bounds[bvs[j]][false].clear();
              }
            }
          }
        }
      }
    }
  }
  
  return false;
}

Node QuantifiersRewriter::computeVarElimination2( Node body, std::vector< Node >& args, QAttributes& qa ){
  Trace("var-elim-quant-debug") << "Compute var elimination for " << body << std::endl;
  std::map< Node, std::map< bool, std::map< Node, bool > > > num_bounds;
  QuantPhaseReq qpr( body );
  std::vector< Node > vars;
  std::vector< Node > subs;
  for( std::map< Node, bool >::iterator it = qpr.d_phase_reqs.begin(); it != qpr.d_phase_reqs.end(); ++it ){
    Trace("var-elim-quant-debug") << "   phase req : " << it->first << " -> " << ( it->second ? "true" : "false" ) << std::endl;
    if( computeVariableElimLit( it->first, it->second, args, vars, subs, num_bounds ) ){
      break;
    }
  }
  
  if( !vars.empty() ){
    Trace("var-elim-quant-debug") << "VE " << vars.size() << "/" << args.size() << std::endl;
    //remake with eliminated nodes
    body = body.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    body = Rewriter::rewrite( body );
    if( !qa.d_ipl.isNull() ){
      qa.d_ipl = qa.d_ipl.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    }
    Trace("var-elim-quant") << "Return " << body << std::endl;
  }else{
    //collect all variables that have only upper/lower bounds
    std::map< Node, bool > elig_vars;
    for( std::map< Node, std::map< bool, std::map< Node, bool > > >::iterator it = num_bounds.begin(); it != num_bounds.end(); ++it ){
      if( it->second.find( true )==it->second.end() ){
        Trace("var-elim-ineq-debug") << "Variable " << it->first << " has only lower bounds." << std::endl;
        elig_vars[it->first] = false;
      }else if( it->second.find( false )==it->second.end() ){
        Trace("var-elim-ineq-debug") << "Variable " << it->first << " has only upper bounds." << std::endl;
        elig_vars[it->first] = true;
      }
    }
    if( !elig_vars.empty() ){
      std::vector< Node > inactive_vars;
      std::map< Node, std::map< int, bool > > visited;
      std::map< Node, int > exclude;
      for( std::map< Node, bool >::iterator it = qpr.d_phase_reqs.begin(); it != qpr.d_phase_reqs.end(); ++it ){
        if( it->first.getKind()==GEQ || it->first.getKind()==GT ){
          exclude[ it->first ] = it->second ? -1 : 1;
          Trace("var-elim-ineq-debug") << "...exclude " << it->first << " at polarity " << exclude[ it->first ] << std::endl;
        }
      }
      //traverse the body, invalidate variables if they occur in places other than the bounds they occur in
      isVariableBoundElig( body, exclude, visited, true, true, elig_vars );
      
      if( !elig_vars.empty() ){
        if( !qa.d_ipl.isNull() ){
          isVariableBoundElig( qa.d_ipl, exclude, visited, false, true, elig_vars );
        }
        for( std::map< Node, bool >::iterator itev = elig_vars.begin(); itev != elig_vars.end(); ++itev ){
          Node v = itev->first;
          Trace("var-elim-ineq-debug") << v << " is eligible for elimination." << std::endl;
          //do substitution corresponding to infinite projection, all literals involving unbounded variable go to true/false
          std::vector< Node > terms;
          std::vector< Node > subs;
          for( std::map< Node, bool >::iterator itb = num_bounds[v][elig_vars[v]].begin(); itb != num_bounds[v][elig_vars[v]].end(); ++itb ){
            Trace("var-elim-ineq-debug") << "  subs : " << itb->first << " -> " << itb->second << std::endl;
            terms.push_back( itb->first );
            subs.push_back( NodeManager::currentNM()->mkConst( itb->second ) );
          }
          body = body.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
          Trace("var-elim-ineq-debug") << "Return " << body << std::endl;
          //eliminate from args
          std::vector< Node >::iterator ita = std::find( args.begin(), args.end(), v );
          Assert( ita!=args.end() );
          args.erase( ita );
        }
      } 
    }
  }
  return body;
}

Node QuantifiersRewriter::computeVarElimination( Node body, std::vector< Node >& args, QAttributes& qa ){
  if( options::varElimQuant() || options::dtVarExpandQuant() ){
    Node prev;
    do{
      prev = body;
      body = computeVarElimination2( body, args, qa );
    }while( prev!=body && !args.empty() );
  }
  return body;
}

Node QuantifiersRewriter::computePrenex( Node body, std::vector< Node >& args, std::vector< Node >& nargs, bool pol, bool prenexAgg ){
  if( body.getKind()==FORALL ){
    if( ( pol || prenexAgg ) && ( options::prenexQuantUser() || body.getNumChildren()==2 ) ){
      std::vector< Node > terms;
      std::vector< Node > subs;
      //for doing prenexing of same-signed quantifiers
      //must rename each variable that already exists
      for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
        terms.push_back( body[0][i] );
        subs.push_back( NodeManager::currentNM()->mkBoundVar( body[0][i].getType() ) );
      }
      if( pol ){
        args.insert( args.end(), subs.begin(), subs.end() );
      }else{
        nargs.insert( nargs.end(), subs.begin(), subs.end() );
      }
      Node newBody = body[1];
      newBody = newBody.substitute( terms.begin(), terms.end(), subs.begin(), subs.end() );
      return newBody;
    }
  //must remove structure
  }else if( prenexAgg && body.getKind()==kind::ITE && body.getType().isBoolean() ){
    Node nn = NodeManager::currentNM()->mkNode( kind::AND,
              NodeManager::currentNM()->mkNode( kind::OR, body[0].notNode(), body[1] ),
              NodeManager::currentNM()->mkNode( kind::OR, body[0], body[2] ) );
    return computePrenex( nn, args, nargs, pol, prenexAgg );
  }else if( prenexAgg && body.getKind()==kind::EQUAL && body[0].getType().isBoolean() ){
    Node nn = NodeManager::currentNM()->mkNode( kind::AND,
              NodeManager::currentNM()->mkNode( kind::OR, body[0].notNode(), body[1] ),
              NodeManager::currentNM()->mkNode( kind::OR, body[0], body[1].notNode() ) );
    return computePrenex( nn, args, nargs, pol, prenexAgg );
  }else if( body.getType().isBoolean() ){
    Assert( body.getKind()!=EXISTS );
    bool childrenChanged = false;
    std::vector< Node > newChildren;
    for( unsigned i=0; i<body.getNumChildren(); i++ ){
      bool newHasPol;
      bool newPol;
      QuantPhaseReq::getPolarity( body, i, true, pol, newHasPol, newPol );
      if( newHasPol ){
        Node n = computePrenex( body[i], args, nargs, newPol, prenexAgg );
        newChildren.push_back( n );
        if( n!=body[i] ){
          childrenChanged = true;
        }
      }else{
        newChildren.push_back( body[i] );
      }
    }
    if( childrenChanged ){
      if( body.getKind()==NOT && newChildren[0].getKind()==NOT ){
        return newChildren[0][0];
      }else{
        return NodeManager::currentNM()->mkNode( body.getKind(), newChildren );
      }
    }
  }
  return body;
}

Node QuantifiersRewriter::computePrenexAgg( Node n, bool topLevel ){
  if( containsQuantifiers( n ) ){
    if( topLevel && options::prenexQuant()==PRENEX_QUANT_DISJ_NORMAL && ( n.getKind()==AND || ( n.getKind()==NOT && n[0].getKind()==OR ) ) ){
      std::vector< Node > children;
      Node nc = n.getKind()==NOT ? n[0] : n;
      for( unsigned i=0; i<nc.getNumChildren(); i++ ){
        Node ncc = computePrenexAgg( nc[i], true );
        if( n.getKind()==NOT ){
          ncc = ncc.negate();        
        }
        children.push_back( ncc );
      }
      return NodeManager::currentNM()->mkNode( AND, children );
    }else if( n.getKind()==NOT ){
      return computePrenexAgg( n[0], false ).negate();
    }else if( n.getKind()==FORALL ){
    /*
      Node nn = computePrenexAgg( n[1], false );
      if( nn!=n[1] ){
        if( n.getNumChildren()==2 ){
          return NodeManager::currentNM()->mkNode( FORALL, n[0], nn );
        }else{
          return NodeManager::currentNM()->mkNode( FORALL, n[0], nn, n[2] );
        }
      }
      */
      std::vector< Node > children;
      if( n[1].getKind()==OR && options::prenexQuant()==PRENEX_QUANT_DISJ_NORMAL ){
        for( unsigned i=0; i<n[1].getNumChildren(); i++ ){
          children.push_back( computePrenexAgg( n[1][i], false ) );
        }
      }else{
        children.push_back( computePrenexAgg( n[1], false ) );
      }
      std::vector< Node > args;
      for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
        args.push_back( n[0][i] );
      }
      std::vector< Node > nargs;
      //for each child, strip top level quant
      for( unsigned i=0; i<children.size(); i++ ){
        if( children[i].getKind()==FORALL ){
          for( unsigned j=0; j<children[i][0].getNumChildren(); j++ ){
            args.push_back( children[i][0][j] );
          }
          children[i] = children[i][1];
        }
      }
      Node nb = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( OR, children );
      return mkForall( args, nb, true );
    }else{
      std::vector< Node > args;
      std::vector< Node > nargs;
      Node nn = computePrenex( n, args, nargs, true, true );
      if( n!=nn ){
        Node nnn = computePrenexAgg( nn, false );
        //merge prenex
        if( nnn.getKind()==FORALL ){
          for( unsigned i=0; i<nnn[0].getNumChildren(); i++ ){
            args.push_back( nnn[0][i] );
          }
          nnn = nnn[1];
          //pos polarity variables are inner
          if( !args.empty() ){
            nnn = mkForall( args, nnn, true );
          }
          args.clear();
        }else if( nnn.getKind()==NOT && nnn[0].getKind()==FORALL ){
          for( unsigned i=0; i<nnn[0][0].getNumChildren(); i++ ){
            nargs.push_back( nnn[0][0][i] );
          }
          nnn = nnn[0][1].negate();
        }
        if( !nargs.empty() ){
          nnn = mkForall( nargs, nnn.negate(), true ).negate();
        }
        if( !args.empty() ){
          nnn = mkForall( args, nnn, true );
        }
        return nnn;
      }else{
        Assert( args.empty() );
        Assert( nargs.empty() );
      }
    }
  }
  return n;
}

Node QuantifiersRewriter::computeSplit( std::vector< Node >& args, Node body, QAttributes& qa ) {
  Assert( body.getKind()==OR );
  size_t var_found_count = 0;
  size_t eqc_count = 0;
  size_t eqc_active = 0;
  std::map< Node, int > var_to_eqc;
  std::map< int, std::vector< Node > > eqc_to_var;
  std::map< int, std::vector< Node > > eqc_to_lit;

  std::vector<Node> lits;

  for( unsigned i=0; i<body.getNumChildren(); i++ ){
    //get variables contained in the literal
    Node n = body[i];
    std::vector< Node > lit_args;
    computeArgVec( args, lit_args, n );
    if( lit_args.empty() ){
      lits.push_back( n );
    }else {
      //collect the equivalence classes this literal belongs to, and the new variables it contributes
      std::vector< int > eqcs;
      std::vector< Node > lit_new_args;
      //for each variable in literal
      for( unsigned j=0; j<lit_args.size(); j++) {
        //see if the variable has already been found
        if (var_to_eqc.find(lit_args[j])!=var_to_eqc.end()) {
          int eqc = var_to_eqc[lit_args[j]];
          if (std::find(eqcs.begin(), eqcs.end(), eqc)==eqcs.end()) {
            eqcs.push_back(eqc);
          }
        }else{
          var_found_count++;
          lit_new_args.push_back(lit_args[j]);
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
      //add variables to equivalence class
      for (unsigned j=0; j<lit_new_args.size(); j++) {
        var_to_eqc[lit_new_args[j]] = eqcz;
        eqc_to_var[eqcz].push_back(lit_new_args[j]);
      }
      //add literal to equivalence class
      eqc_to_lit[eqcz].push_back(n);
    }
  }
  if ( eqc_active>1 || !lits.empty() || var_to_eqc.size()!=args.size() ){
    Trace("clause-split-debug") << "Split quantified formula with body " << body << std::endl;
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
      Node body = it->second.size()==1 ? it->second[0] : NodeManager::currentNM()->mkNode( OR, it->second );
      Node fa = NodeManager::currentNM()->mkNode( FORALL, bvl, body );
      lits.push_back(fa);
    }
    Assert( !lits.empty() );
    Node nf = lits.size()==1 ? lits[0] : NodeManager::currentNM()->mkNode(OR,lits);
    Trace("clause-split-debug") << "Made node : " << nf << std::endl;
    return nf;
  }else{
    return mkForAll( args, body, qa );
  }
}

Node QuantifiersRewriter::mkForAll( std::vector< Node >& args, Node body, QAttributes& qa ){
  if( args.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
    children.push_back( body );
    if( !qa.d_ipl.isNull() ){
      children.push_back( qa.d_ipl );
    }
    return NodeManager::currentNM()->mkNode( kind::FORALL, children );
  }
}
Node QuantifiersRewriter::mkForall( std::vector< Node >& args, Node body, bool marked ) {
  if( args.empty() ){
    return body;
  }else{
    std::vector< Node > children;
    children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
    children.push_back( body );
    std::vector< Node > iplc;
    if( marked ){
      Node avar = NodeManager::currentNM()->mkSkolem( "id", NodeManager::currentNM()->booleanType() );
      QuantIdNumAttribute ida;
      avar.setAttribute(ida,0);
      iplc.push_back( NodeManager::currentNM()->mkNode( INST_ATTRIBUTE, avar ) );
    }
    if( !iplc.empty() ){
      children.push_back( NodeManager::currentNM()->mkNode( INST_PATTERN_LIST, iplc ) );
    }
    return NodeManager::currentNM()->mkNode( FORALL, children );
  }
}

//computes miniscoping, also eliminates variables that do not occur free in body
Node QuantifiersRewriter::computeMiniscoping( std::vector< Node >& args, Node body, QAttributes& qa ){
  if( body.getKind()==FORALL ){
    //combine prenex
    std::vector< Node > newArgs;
    newArgs.insert( newArgs.end(), args.begin(), args.end() );
    for( unsigned i=0; i<body[0].getNumChildren(); i++ ){
      newArgs.push_back( body[0][i] );
    }
    return mkForAll( newArgs, body[1], qa );
  }else if( body.getKind()==AND ){
    if( options::miniscopeQuant() ){
      //break apart
      NodeBuilder<> t(kind::AND);
      for( unsigned i=0; i<body.getNumChildren(); i++ ){
        t << computeMiniscoping( args, body[i], qa );
      }
      Node retVal = t;
      return retVal;
    }
  }else if( body.getKind()==OR ){
    if( options::quantSplit() ){
      //splitting subsumes free variable miniscoping, apply it with higher priority
      return computeSplit( args, body, qa );
    }else if( options::miniscopeQuantFreeVar() ){
      Node newBody = body;
      NodeBuilder<> body_split(kind::OR);
      NodeBuilder<> tb(kind::OR);
      for( unsigned i=0; i<body.getNumChildren(); i++ ){
        Node trm = body[i];
        if( TermDb::containsTerms( body[i], args ) ){
          tb << trm;
        }else{
          body_split << trm;
        }
      }
      if( tb.getNumChildren()==0 ){
        return body_split;
      }else if( body_split.getNumChildren()>0 ){
        newBody = tb.getNumChildren()==1 ? tb.getChild( 0 ) : tb;
        std::vector< Node > activeArgs;
        computeArgVec2( args, activeArgs, newBody, qa.d_ipl );
        body_split << mkForAll( activeArgs, newBody, qa );
        return body_split.getNumChildren()==1 ? body_split.getChild( 0 ) : body_split;
      }
    }
  }else if( body.getKind()==NOT ){
    Assert( isLiteral( body[0] ) );
  }
  //remove variables that don't occur
  std::vector< Node > activeArgs;
  computeArgVec2( args, activeArgs, body, qa.d_ipl );
  return mkForAll( activeArgs, body, qa );
}

Node QuantifiersRewriter::computeAggressiveMiniscoping( std::vector< Node >& args, Node body ){
  std::map<Node, std::vector<Node> > varLits;
  std::map<Node, std::vector<Node> > litVars;
  if (body.getKind() == OR) {
    Trace("ag-miniscope") << "compute aggressive miniscoping on " << body << std::endl;
    for (size_t i = 0; i < body.getNumChildren(); i++) {
      std::vector<Node> activeArgs;
      computeArgVec(args, activeArgs, body[i]);
      for (unsigned j = 0; j < activeArgs.size(); j++) {
        varLits[activeArgs[j]].push_back(body[i]);
      }
      std::vector<Node>& lit_body_i = litVars[body[i]];
      std::vector<Node>::iterator lit_body_i_begin = lit_body_i.begin();
      std::vector<Node>::const_iterator active_begin = activeArgs.begin();
      std::vector<Node>::const_iterator active_end = activeArgs.end();
      lit_body_i.insert(lit_body_i_begin, active_begin, active_end);
    }
    //find the variable in the least number of literals
    Node bestVar;
    for( std::map< Node, std::vector<Node> >::iterator it = varLits.begin(); it != varLits.end(); ++it ){
      if( bestVar.isNull() || varLits[bestVar].size()>it->second.size() ){
        bestVar = it->first;
      }
    }
    Trace("ag-miniscope-debug") << "Best variable " << bestVar << " occurs in " << varLits[bestVar].size() << "/ " << body.getNumChildren() << " literals." << std::endl;
    if( !bestVar.isNull() && varLits[bestVar].size()<body.getNumChildren() ){
      //we can miniscope
      Trace("ag-miniscope") << "Miniscope on " << bestVar << std::endl;
      //make the bodies
      std::vector<Node> qlit1;
      qlit1.insert( qlit1.begin(), varLits[bestVar].begin(), varLits[bestVar].end() );
      std::vector<Node> qlitt;
      //for all literals not containing bestVar
      for( size_t i=0; i<body.getNumChildren(); i++ ){
        if( std::find( qlit1.begin(), qlit1.end(), body[i] )==qlit1.end() ){
          qlitt.push_back( body[i] );
        }
      }
      //make the variable lists
      std::vector<Node> qvl1;
      std::vector<Node> qvl2;
      std::vector<Node> qvsh;
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
      std::vector<Node> qlitsh;
      std::vector<Node> qlit2;
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
  QAttributes qa;
  return mkForAll( args, body, qa );
}

bool QuantifiersRewriter::doOperation( Node q, int computeOption, QAttributes& qa ){
  bool is_strict_trigger = qa.d_hasPattern && options::userPatternsQuant()==USER_PAT_MODE_TRUST;
  bool is_std = !qa.d_sygus && !qa.d_quant_elim && !qa.isFunDef() && !is_strict_trigger;
  if( computeOption==COMPUTE_ELIM_SYMBOLS ){
    return true;
  }else if( computeOption==COMPUTE_MINISCOPING ){
    return is_std;
  }else if( computeOption==COMPUTE_AGGRESSIVE_MINISCOPING ){
    return options::aggressiveMiniscopeQuant() && is_std;
  }else if( computeOption==COMPUTE_PROCESS_TERMS ){
    return options::condRewriteQuant();
  }else if( computeOption==COMPUTE_COND_SPLIT ){
    return ( options::iteDtTesterSplitQuant() || options::condVarSplitQuant() ) && !is_strict_trigger;
  }else if( computeOption==COMPUTE_PRENEX ){
    return options::prenexQuant()!=PRENEX_QUANT_NONE && !options::aggressiveMiniscopeQuant() && is_std;
  }else if( computeOption==COMPUTE_VAR_ELIMINATION ){
    return ( options::varElimQuant() || options::dtVarExpandQuant() ) && is_std;
  }else{
    return false;
  }
}

//general method for computing various rewrites
Node QuantifiersRewriter::computeOperation( Node f, int computeOption, QAttributes& qa ){
  Trace("quantifiers-rewrite-debug") << "Compute operation " << computeOption << " on " << f << " " << qa.d_qid_num << std::endl;
  std::vector< Node > args;
  for( unsigned i=0; i<f[0].getNumChildren(); i++ ){
    args.push_back( f[0][i] );
  }
  Node n = f[1];
  if( computeOption==COMPUTE_ELIM_SYMBOLS ){
    n = computeElimSymbols( n );
  }else if( computeOption==COMPUTE_MINISCOPING ){
    if( options::prenexQuant()==PRENEX_QUANT_DISJ_NORMAL || options::prenexQuant()==PRENEX_QUANT_NORMAL ){
      if( !qa.d_qid_num.isNull() ){
        //already processed this, return self
        return f;
      }
    }
    //return directly
    return computeMiniscoping( args, n, qa );
  }else if( computeOption==COMPUTE_AGGRESSIVE_MINISCOPING ){
    return computeAggressiveMiniscoping( args, n );
  }else if( computeOption==COMPUTE_PROCESS_TERMS ){
    std::vector< Node > new_conds;
    n = computeProcessTerms( n, args, new_conds, f, qa );
    if( !new_conds.empty() ){
      new_conds.push_back( n );
      n = NodeManager::currentNM()->mkNode( OR, new_conds );
    }
  }else if( computeOption==COMPUTE_COND_SPLIT ){
    n = computeCondSplit( n, qa );
  }else if( computeOption==COMPUTE_PRENEX ){
    if( options::prenexQuant()==PRENEX_QUANT_DISJ_NORMAL || options::prenexQuant()==PRENEX_QUANT_NORMAL ){
      //will rewrite at preprocess time
      return f;
    }else{
      std::vector< Node > nargs;
      n = computePrenex( n, args, nargs, true, false );
      Assert( nargs.empty() );
    }
  }else if( computeOption==COMPUTE_VAR_ELIMINATION ){
    n = computeVarElimination( n, args, qa );
  }
  Trace("quantifiers-rewrite-debug") << "Compute Operation: return " << n << ", " << args.size() << std::endl;
  if( f[1]==n && args.size()==f[0].getNumChildren() ){
    return f;
  }else{
    if( args.empty() ){
      return n;
    }else{
      std::vector< Node > children;
      children.push_back( NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args ) );
      children.push_back( n );
      if( !qa.d_ipl.isNull() && args.size()==f[0].getNumChildren() ){
        children.push_back( qa.d_ipl );
      }
      return NodeManager::currentNM()->mkNode(kind::FORALL, children );
    }
  }
}


Node QuantifiersRewriter::rewriteRewriteRule( Node r ) {
  Kind rrkind = r[2].getKind();

  //guards, pattern, body

  //   Replace variables by Inst_* variable and tag the terms that contain them
  std::vector<Node> vars;
  vars.reserve(r[0].getNumChildren());
  for( Node::const_iterator v = r[0].begin(); v != r[0].end(); ++v ){
    vars.push_back(*v);
  };

  // Body/Remove_term/Guards/Triggers
  Node body = r[2][1];
  TNode new_terms = r[2][1];
  std::vector<Node> guards;
  std::vector<Node> pattern;
  Node true_node = NodeManager::currentNM()->mkConst(true);
  // shortcut
  TNode head = r[2][0];
  switch(rrkind){
  case kind::RR_REWRITE:
    // Equality
    pattern.push_back( head );
    body = head.eqNode(body);
    break;
  case kind::RR_REDUCTION:
  case kind::RR_DEDUCTION:
    // Add head to guards and pattern
    switch(head.getKind()){
    case kind::AND:
      for( unsigned i = 0; i<head.getNumChildren(); i++ ){
        guards.push_back(head[i]);
        pattern.push_back(head[i]);
      }
      break;
    default:
      if( head!=true_node ){
        guards.push_back(head);
        pattern.push_back( head );
      }
      break;
    }
    break;
  default:
    Unreachable("RewriteRules can be of only three kinds");
    break;
  }
  // Add the other guards
  TNode g = r[1];
  switch(g.getKind()){
  case kind::AND:
    for( unsigned i = 0; i<g.getNumChildren(); i++ ){
      guards.push_back(g[i]);
    }
    break;
  default:
    if( g != true_node ){
      guards.push_back( g );
    }
    break;
  }
  // Add the other triggers
  if( r[2].getNumChildren() >= 3 ){
    for( unsigned i=0; i<r[2][2][0].getNumChildren(); i++ ) {
      pattern.push_back( r[2][2][0][i] );
    }
  }

  Trace("rr-rewrite") << "Rule is " << r << std::endl;
  Trace("rr-rewrite") << "Head is " << head << std::endl;
  Trace("rr-rewrite") << "Patterns are ";
  for( unsigned i=0; i<pattern.size(); i++ ){
    Trace("rr-rewrite") << pattern[i] << " ";
  }
  Trace("rr-rewrite") << std::endl;

  NodeBuilder<> forallB(kind::FORALL);
  forallB << r[0];
  Node gg = guards.size()==0 ? true_node : ( guards.size()==1 ? guards[0] : NodeManager::currentNM()->mkNode( AND, guards ) );
  gg = NodeManager::currentNM()->mkNode( OR, gg.negate(), body );
  gg = Rewriter::rewrite( gg );
  forallB << gg;
  NodeBuilder<> patternB(kind::INST_PATTERN);
  patternB.append(pattern);
  NodeBuilder<> patternListB(kind::INST_PATTERN_LIST);
  //the entire rewrite rule is the first pattern
  if( options::quantRewriteRules() ){
    patternListB << NodeManager::currentNM()->mkNode( INST_ATTRIBUTE, r );
  }
  patternListB << static_cast<Node>(patternB);
  forallB << static_cast<Node>(patternListB);
  Node rn = (Node) forallB;

  return rn;
}

struct ContainsQuantAttributeId {};
typedef expr::Attribute<ContainsQuantAttributeId, uint64_t> ContainsQuantAttribute;

// check if the given node contains a universal quantifier
bool QuantifiersRewriter::containsQuantifiers( Node n ){
  if( n.hasAttribute(ContainsQuantAttribute()) ){
    return n.getAttribute(ContainsQuantAttribute())==1;
  }else if( n.getKind() == kind::FORALL ){
    return true;
  }else{
    bool cq = false;
    for( unsigned i = 0; i < n.getNumChildren(); ++i ){
      if( containsQuantifiers( n[i] ) ){
        cq = true;
        break;
      }
    }
    ContainsQuantAttribute cqa;
    n.setAttribute(cqa, cq ? 1 : 0);
    return cq;
  }
}
bool QuantifiersRewriter::isPrenexNormalForm( Node n ) {
  if( n.getKind()==FORALL ){
    return n[1].getKind()!=FORALL && isPrenexNormalForm( n[1] );
  }else if( n.getKind()==NOT ){
    return n[0].getKind()!=NOT && isPrenexNormalForm( n[0] );
  }else{
    return !containsQuantifiers( n );
  }
}

Node QuantifiersRewriter::preSkolemizeQuantifiers( Node n, bool polarity, std::vector< TypeNode >& fvTypes, std::vector< TNode >& fvs ){
  Trace("pre-sk") << "Pre-skolem " << n << " " << polarity << " " << fvs.size() << endl;
  if( n.getKind()==kind::NOT ){
    Node nn = preSkolemizeQuantifiers( n[0], !polarity, fvTypes, fvs );
    return nn.negate();
  }else if( n.getKind()==kind::FORALL ){
    if( polarity ){
      if( options::preSkolemQuant() && options::preSkolemQuantNested() ){
        vector< Node > children;
        children.push_back( n[0] );
        //add children to current scope
        std::vector< TypeNode > fvt;
        std::vector< TNode > fvss;
        fvt.insert( fvt.begin(), fvTypes.begin(), fvTypes.end() );
        fvss.insert( fvss.begin(), fvs.begin(), fvs.end() );
        for( int i=0; i<(int)n[0].getNumChildren(); i++ ){
          fvt.push_back( n[0][i].getType() );
          fvss.push_back( n[0][i] );
        }
        //process body
        children.push_back( preSkolemizeQuantifiers( n[1], polarity, fvt, fvss ) );
        if( n.getNumChildren()==3 ){
          children.push_back( n[2] );
        }
        //return processed quantifier
        return NodeManager::currentNM()->mkNode( kind::FORALL, children );
      }
    }else{
      //process body
      Node nn = preSkolemizeQuantifiers( n[1], polarity, fvTypes, fvs );
      std::vector< Node > sk;
      Node sub;
      std::vector< unsigned > sub_vars;
      //return skolemized body
      return TermDb::mkSkolemizedBody( n, nn, fvTypes, fvs, sk, sub, sub_vars );
    }
  }else{
    //check if it contains a quantifier as a subterm
    //if so, we will write this node
    if( containsQuantifiers( n ) ){
      if( ( n.getKind()==kind::ITE && n.getType().isBoolean() ) || ( n.getKind()==kind::EQUAL && n[0].getType().isBoolean() ) ){
        if( options::preSkolemQuantAgg() ){
          Node nn;
          //must remove structure
          if( n.getKind()==kind::ITE ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                  NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n[1] ),
                  NodeManager::currentNM()->mkNode( kind::OR, n[0], n[2] ) );
          }else if( n.getKind()==kind::EQUAL ){
            nn = NodeManager::currentNM()->mkNode( kind::AND,
                  NodeManager::currentNM()->mkNode( kind::OR, n[0].notNode(), n.getKind()==kind::XOR ? n[1].notNode() : n[1] ),
                  NodeManager::currentNM()->mkNode( kind::OR, n[0], n.getKind()==kind::XOR ? n[1] : n[1].notNode() ) );
          }
          return preSkolemizeQuantifiers( nn, polarity, fvTypes, fvs );
        }
      }else if( n.getKind()==kind::AND || n.getKind()==kind::OR ){
        vector< Node > children;
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          children.push_back( preSkolemizeQuantifiers( n[i], polarity, fvTypes, fvs ) );
        }
        return NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }
  }
  return n;
}


Node QuantifiersRewriter::preprocess( Node n, bool isInst ) {
  Node prev = n;
  if( n.getKind() == kind::REWRITE_RULE ){
    n = quantifiers::QuantifiersRewriter::rewriteRewriteRule( n );
  }else{
    if( options::preSkolemQuant() ){
      if( !isInst || !options::preSkolemQuantNested() ){
        Trace("quantifiers-preprocess-debug") << "Pre-skolemize " << n << "..." << std::endl;
        //apply pre-skolemization to existential quantifiers
        std::vector< TypeNode > fvTypes;
        std::vector< TNode > fvs;
        n = quantifiers::QuantifiersRewriter::preSkolemizeQuantifiers( prev, true, fvTypes, fvs );
      }
    }
  }
  //pull all quantifiers globally
  if( options::prenexQuant()==PRENEX_QUANT_DISJ_NORMAL || options::prenexQuant()==PRENEX_QUANT_NORMAL ){
    Trace("quantifiers-prenex") << "Prenexing : " << n << std::endl;
    n = quantifiers::QuantifiersRewriter::computePrenexAgg( n, true );
    n = Rewriter::rewrite( n );
    Trace("quantifiers-prenex") << "Prenexing returned : " << n << std::endl;
    //Assert( isPrenexNormalForm( n ) );
  }
  if( n!=prev ){       
    Trace("quantifiers-preprocess") << "Preprocess " << prev << std::endl;
    Trace("quantifiers-preprocess") << "..returned " << n << std::endl;
  }
  return n;
}

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

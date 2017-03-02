/*********************                                                        */
/*! \file fun_def_process.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements pre-process steps for well-defined functions
 **/

#include <vector>

#include "theory/quantifiers/fun_def_process.h"
#include "theory/rewriter.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quant_util.h"
#include "proof/proof_manager.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;


void FunDefFmf::simplify( std::vector< Node >& assertions, bool doRewrite ) {
  std::vector< int > fd_assertions;
  std::map< int, Node > subs_head;
  //first pass : find defined functions, transform quantifiers
  for( unsigned i=0; i<assertions.size(); i++ ){
    Node n = TermDb::getFunDefHead( assertions[i] );
    if( !n.isNull() ){
      Assert( n.getKind()==APPLY_UF );
      Node f = n.getOperator();

      //check if already defined, if so, throw error
      if( d_sorts.find( f )!=d_sorts.end() ){
        Message() << "Cannot define function " << f << " more than once." << std::endl;
        exit( 0 );
      }

      Node bd = TermDb::getFunDefBody( assertions[i] );
      Trace("fmf-fun-def-debug") << "Process function " << n << ", body = " << bd << std::endl;
      if( !bd.isNull() ){
        d_funcs.push_back( f );
        bd = NodeManager::currentNM()->mkNode( EQUAL, n, bd );

        //create a sort S that represents the inputs of the function
        std::stringstream ss;
        ss << "I_" << f;
        TypeNode iType = NodeManager::currentNM()->mkSort( ss.str() );
        AbsTypeFunDefAttribute atfda;
        iType.setAttribute(atfda,true);
        d_sorts[f] = iType;

        //create functions f1...fn mapping from this sort to concrete elements
        for( unsigned j=0; j<n.getNumChildren(); j++ ){
          TypeNode typ = NodeManager::currentNM()->mkFunctionType( iType, n[j].getType() );
          std::stringstream ss;
          ss << f << "_arg_" << j;
          d_input_arg_inj[f].push_back( NodeManager::currentNM()->mkSkolem( ss.str(), typ, "op created during fun def fmf" ) );
        }

        //construct new quantifier forall S. F[f1(S)/x1....fn(S)/xn]
        std::vector< Node > children;
        Node bv = NodeManager::currentNM()->mkBoundVar("?i", iType );
        Node bvl = NodeManager::currentNM()->mkNode( kind::BOUND_VAR_LIST, bv );
        std::vector< Node > subs;
        std::vector< Node > vars;
        for( unsigned j=0; j<n.getNumChildren(); j++ ){
          vars.push_back( n[j] );
          subs.push_back( NodeManager::currentNM()->mkNode( APPLY_UF, d_input_arg_inj[f][j], bv ) );
        }
        bd = bd.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
        subs_head[i] = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );

        Trace("fmf-fun-def") << "FMF fun def: FUNCTION : rewrite " << assertions[i] << std::endl;
        Trace("fmf-fun-def") << "  to " << std::endl;
        Node new_q = NodeManager::currentNM()->mkNode( FORALL, bvl, bd );
        new_q = Rewriter::rewrite( new_q );
        PROOF( ProofManager::currentPM()->addDependence(new_q, assertions[i]); );
        assertions[i] = new_q;
        Trace("fmf-fun-def") << "  " << assertions[i] << std::endl;
        fd_assertions.push_back( i );
      }else{
        //can be, e.g. in corner cases forall x. f(x)=f(x), forall x. f(x)=f(x)+1
      }
    }
  }
  //second pass : rewrite assertions
  for( unsigned i=0; i<assertions.size(); i++ ){
    int is_fd = std::find( fd_assertions.begin(), fd_assertions.end(), i )!=fd_assertions.end() ? 1 : 0;
    //constant boolean function definitions do not add domain constraints
    if( is_fd==0 || ( is_fd==1 && assertions[i][1].getKind()==EQUAL ) ){
      std::vector< Node > constraints;
      Trace("fmf-fun-def-rewrite") << "Rewriting " << assertions[i] << ", is_fd = " << is_fd << std::endl;
      Node n = simplifyFormula( assertions[i], true, true, constraints, is_fd==1 ? subs_head[i] : Node::null(), is_fd );
      Assert( constraints.empty() );
      if( n!=assertions[i] ){
        n = Rewriter::rewrite( n );
        Trace("fmf-fun-def-rewrite") << "FMF fun def : rewrite " << assertions[i] << std::endl;
        Trace("fmf-fun-def-rewrite") << "  to " << std::endl;
        Trace("fmf-fun-def-rewrite") << "  " << n << std::endl;
        PROOF( ProofManager::currentPM()->addDependence(n, assertions[i]); );
        assertions[i] = n;
      }
    }
  }
}

//is_fun_def 1 : top of fun-def, 2 : top of fun-def body, 0 : not top
Node FunDefFmf::simplifyFormula( Node n, bool pol, bool hasPol, std::vector< Node >& constraints, Node hd, int is_fun_def ) {
  Trace("fmf-fun-def-debug") << "Simplify " << n << " " << pol << " " << hasPol << " " << is_fun_def << std::endl;
  if( n.getKind()==FORALL ){
    Node c = simplifyFormula( n[1], pol, hasPol, constraints, hd, is_fun_def );
    //append prenex to constraints
    for( unsigned i=0; i<constraints.size(); i++ ){
      constraints[i] = NodeManager::currentNM()->mkNode( FORALL, n[0], constraints[i] );
      constraints[i] = Rewriter::rewrite( constraints[i] );
    }
    if( c!=n[1] ){
      return NodeManager::currentNM()->mkNode( FORALL, n[0], c );
    }else{
      return n;
    }
  }else{
    Node nn = n;
    bool isBool = n.getType().isBoolean();
    if( isBool && n.getKind()!=APPLY_UF && is_fun_def!=2 ){
      std::vector< Node > children;
      bool childChanged = false;
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        Node c = n[i];
        //do not process LHS of definition
        if( is_fun_def!=1 || c!=hd ){
          bool newHasPol;
          bool newPol;
          QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
          //get child constraints
          std::vector< Node > cconstraints;
          c = simplifyFormula( n[i], newPol, newHasPol, cconstraints, hd, is_fun_def==1 ? 2 : 0 );
          constraints.insert( constraints.end(), cconstraints.begin(), cconstraints.end() );
        }
        children.push_back( c );
        childChanged = c!=n[i] || childChanged;
      }
      if( childChanged ){
        nn = NodeManager::currentNM()->mkNode( n.getKind(), children );
      }
    }else{
      //simplify term
      simplifyTerm( n, constraints );
    }
    if( !constraints.empty() && isBool && hasPol ){
      std::vector< Node > c;
      c.push_back( nn );
      //conjoin with current
      for( unsigned i=0; i<constraints.size(); i++ ){
        if( pol ){
          c.push_back( constraints[i] );
        }else{
          c.push_back( constraints[i].negate() );
        }
      }
      constraints.clear();
      return c.size()==1 ? c[0] : NodeManager::currentNM()->mkNode( pol ? AND : OR, c );
    }else{
      return nn;
    }
  }
}

void FunDefFmf::simplifyTerm( Node n, std::vector< Node >& constraints ) {
  Trace("fmf-fun-def-debug") << "Simplify term " << n << std::endl;
  if( n.getKind()==ITE ){
    simplifyTerm( n[0], constraints );
    std::vector< Node > ccons1;
    std::vector< Node > ccons2;
    simplifyTerm( n[1], ccons1 );
    simplifyTerm( n[2], ccons2 );
    if( !ccons1.empty() || !ccons2.empty() ){
      Node n1 = ccons1.empty() ? NodeManager::currentNM()->mkConst( true ) : ( ccons1.size()==1 ? ccons1[0] : NodeManager::currentNM()->mkNode( AND, ccons1 ) );
      Node n2 = ccons2.empty() ? NodeManager::currentNM()->mkConst( true ) : ( ccons2.size()==1 ? ccons2[0] : NodeManager::currentNM()->mkNode( AND, ccons2 ) );
      constraints.push_back( NodeManager::currentNM()->mkNode( ITE, n[0], n1, n2 ) );
    }
  }else{
    if( n.getKind()==APPLY_UF ){
      //check if f is defined, if so, we must enforce domain constraints for this f-application
      Node f = n.getOperator();
      std::map< Node, TypeNode >::iterator it = d_sorts.find( f );
      if( it!=d_sorts.end() ){
        //create existential
        Node z = NodeManager::currentNM()->mkBoundVar("?z", it->second );
        Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, z );
        std::vector< Node > children;
        for( unsigned j=0; j<n.getNumChildren(); j++ ){
          Node uz = NodeManager::currentNM()->mkNode( APPLY_UF, d_input_arg_inj[f][j], z );
          children.push_back( uz.eqNode( n[j] ) );
        }
        Node bd = children.size()==1 ? children[0] : NodeManager::currentNM()->mkNode( AND, children );
        bd = bd.negate();
        Node ex = NodeManager::currentNM()->mkNode( FORALL, bvl, bd );
        ex = ex.negate();
        constraints.push_back( ex );
        Trace("fmf-fun-def-debug") << "---> add constraint " << ex << std::endl;
      }
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      simplifyTerm( n[i], constraints );
    }
  }
}

/*********************                                                        */
/*! \file quant_util.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifier utilities
 **/

#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;


unsigned QuantifiersModule::needsModel( Theory::Effort e ) {
  return QuantifiersEngine::QEFFORT_NONE;
}

eq::EqualityEngine * QuantifiersModule::getEqualityEngine() {
  return d_quantEngine->getMasterEqualityEngine();
}

bool QuantifiersModule::areEqual( TNode n1, TNode n2 ) {
  return d_quantEngine->getEqualityQuery()->areEqual( n1, n2 );
}

bool QuantifiersModule::areDisequal( TNode n1, TNode n2 ) {
  return d_quantEngine->getEqualityQuery()->areDisequal( n1, n2 );
}

TNode QuantifiersModule::getRepresentative( TNode n ) {
  return d_quantEngine->getEqualityQuery()->getRepresentative( n );
}

quantifiers::TermDb * QuantifiersModule::getTermDatabase() {
  return d_quantEngine->getTermDatabase();
}

bool QuantArith::getMonomial( Node n, Node& c, Node& v ){
  if( n.getKind()==MULT && n.getNumChildren()==2 && n[0].isConst() ){
    c = n[0];
    v = n[1];
    return true;
  }else{
    return false;
  }
}
bool QuantArith::getMonomial( Node n, std::map< Node, Node >& msum ) {
  if( n.isConst() ){
    if( msum.find(Node::null())==msum.end() ){
      msum[Node::null()] = n;
      return true;
    }
  }else if( n.getKind()==MULT && n.getNumChildren()==2 && n[0].isConst() ){
    if( msum.find(n[1])==msum.end() ){
      msum[n[1]] = n[0];
      return true;
    }
  }else{
    if( msum.find(n)==msum.end() ){
      msum[n] = Node::null();
      return true;
    }
  }
  return false;
}

bool QuantArith::getMonomialSum( Node n, std::map< Node, Node >& msum ) {
  if ( n.getKind()==PLUS ){
    for( unsigned i=0; i<n.getNumChildren(); i++) {
      if (!getMonomial( n[i], msum )){
        return false;
      }
    }
    return true;
  }else{
    return getMonomial( n, msum );
  }
}

bool QuantArith::getMonomialSumLit( Node lit, std::map< Node, Node >& msum ) {
  if( lit.getKind()==GEQ || lit.getKind()==EQUAL ){
    if( getMonomialSum( lit[0], msum ) ){
      if( lit[1].isConst() && lit[1].getConst<Rational>().isZero() ){
        return true;
      }else{
        //subtract the other side
        std::map< Node, Node > msum2;
        if( getMonomialSum( lit[1], msum2 ) ){
          for( std::map< Node, Node >::iterator it = msum2.begin(); it != msum2.end(); ++it ){
            std::map< Node, Node >::iterator it2 = msum.find( it->first );
            if( it2!=msum.end() ){
              Node r = NodeManager::currentNM()->mkNode( MINUS, it2->second.isNull() ? NodeManager::currentNM()->mkConst( Rational(1) ) : it2->second,
                                                                it->second.isNull() ? NodeManager::currentNM()->mkConst( Rational(1) ) : it->second );
              msum[it->first] = Rewriter::rewrite( r );
            }else{
              msum[it->first] = it->second.isNull() ? NodeManager::currentNM()->mkConst( Rational(-1) ) : negate( it->second );
            }
          }
          return true;
        }
      }
    }
  }
  return false;
}

Node QuantArith::mkNode( std::map< Node, Node >& msum ) {
  std::vector< Node > children;
  for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
    Node m;
    if( !it->first.isNull() ){
      if( !it->second.isNull() ){
        m = NodeManager::currentNM()->mkNode( MULT, it->second, it->first );
      }else{
        m = it->first;
      }
    }else{
      Assert( !it->second.isNull() );
      m = it->second;
    }
    children.push_back(m);
  }
  return children.size()>1 ? NodeManager::currentNM()->mkNode( PLUS, children ) : (children.size()==1 ? children[0] : NodeManager::currentNM()->mkConst( Rational(0) ));
}

// given (msum <k> 0), solve (veq_c * v <k> val) or (val <k> veq_c * v), where:
// veq_c is either null (meaning 1), or positive.
// return value 1: veq_c*v is RHS, -1: veq_c*v is LHS, 0: failed.
int QuantArith::isolate( Node v, std::map< Node, Node >& msum, Node & veq_c, Node & val, Kind k ) {
  std::map< Node, Node >::iterator itv = msum.find( v );
  if( itv!=msum.end() ){
    std::vector< Node > children;
    Rational r = itv->second.isNull() ? Rational(1) : itv->second.getConst<Rational>();
    if ( r.sgn()!=0 ){
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        if( it->first!=v ){
          Node m;
          if( !it->first.isNull() ){
            if ( !it->second.isNull() ){
              m = NodeManager::currentNM()->mkNode( MULT, it->second, it->first );
            }else{
              m = it->first;
            }
          }else{
            m = it->second;
          }
          children.push_back(m);
        }
      }
      val = children.size()>1 ? NodeManager::currentNM()->mkNode( PLUS, children ) :
                                (children.size()==1 ? children[0] : NodeManager::currentNM()->mkConst( Rational(0) ));
      if( !r.isOne() && !r.isNegativeOne() ){
        if( v.getType().isInteger() ){
          veq_c = NodeManager::currentNM()->mkConst( r.abs() );
        }else{
          val = NodeManager::currentNM()->mkNode( MULT, val, NodeManager::currentNM()->mkConst( Rational(1) / r.abs() ) );
        }
      }
      if( r.sgn()==1 ){
        val = negate(val);
      }else{
        val = Rewriter::rewrite( val );
      }
      return ( r.sgn()==1 || k==EQUAL ) ? 1 : -1;
    }
  }
  return 0;
}

int QuantArith::isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k, bool doCoeff ) {
  Node veq_c;
  Node val;
  //isolate v in the (in)equality
  int ires = isolate( v, msum, veq_c, val, k );
  if( ires!=0 ){
    Node vc = v;
    if( !veq_c.isNull() ){
      if( doCoeff ){
        vc = NodeManager::currentNM()->mkNode( MULT, veq_c, vc );
      }else{
        return 0;
      }
    }
    bool inOrder = ires==1;
    veq = NodeManager::currentNM()->mkNode( k, inOrder ? vc : val, inOrder ? val : vc );
  }
  return ires;
}

Node QuantArith::solveEqualityFor( Node lit, Node v ) {
  Assert( lit.getKind()==EQUAL || lit.getKind()==IFF );
  //first look directly at sides
  TypeNode tn = lit[0].getType();
  for( unsigned r=0; r<2; r++ ){
    if( lit[r]==v ){
      return lit[1-r];
    }
  }
  if( tn.isReal() ){
    if( quantifiers::TermDb::containsTerm( lit, v ) ){
      std::map< Node, Node > msum;
      if( QuantArith::getMonomialSumLit( lit, msum ) ){
        Node val, veqc;
        if( QuantArith::isolate( v, msum, veqc, val, EQUAL )!=0 ){
          if( veqc.isNull() ){
            return val;
          }
        }
      }
    }
  }
  return Node::null();
}

Node QuantArith::negate( Node t ) {
  Node tt = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( Rational(-1) ), t );
  tt = Rewriter::rewrite( tt );
  return tt;
}

Node QuantArith::offset( Node t, int i ) {
  Node tt = NodeManager::currentNM()->mkNode( PLUS, NodeManager::currentNM()->mkConst( Rational(i) ), t );
  tt = Rewriter::rewrite( tt );
  return tt;
}

void QuantArith::debugPrintMonomialSum( std::map< Node, Node >& msum, const char * c ) {
  for(std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
    Trace(c) << "  ";
    if( !it->second.isNull() ){
      Trace(c) << it->second;
      if( !it->first.isNull() ){
        Trace(c) << " * ";
      }
    }
    if( !it->first.isNull() ){
      Trace(c) << it->first;
    }
    Trace(c) << std::endl;
  }
  Trace(c) << std::endl;
}


void QuantRelevance::registerQuantifier( Node f ){
  //compute symbols in f
  std::vector< Node > syms;
  computeSymbols( f[1], syms );
  d_syms[f].insert( d_syms[f].begin(), syms.begin(), syms.end() );
  //set initial relevance
  int minRelevance = -1;
  for( int i=0; i<(int)syms.size(); i++ ){
    d_syms_quants[ syms[i] ].push_back( f );
    int r = getRelevance( syms[i] );
    if( r!=-1 && ( minRelevance==-1 || r<minRelevance ) ){
      minRelevance = r;
    }
  }
  if( minRelevance!=-1 ){
    setRelevance( f, minRelevance+1 );
  }
}


/** compute symbols */
void QuantRelevance::computeSymbols( Node n, std::vector< Node >& syms ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( std::find( syms.begin(), syms.end(), op )==syms.end() ){
      syms.push_back( op );
    }
  }
  if( n.getKind()!=FORALL ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeSymbols( n[i], syms );
    }
  }
}

/** set relevance */
void QuantRelevance::setRelevance( Node s, int r ){
  if( d_computeRel ){
    int rOld = getRelevance( s );
    if( rOld==-1 || r<rOld ){
      d_relevance[s] = r;
      if( s.getKind()==FORALL ){
        for( int i=0; i<(int)d_syms[s].size(); i++ ){
          setRelevance( d_syms[s][i], r );
        }
      }else{
        for( int i=0; i<(int)d_syms_quants[s].size(); i++ ){
          setRelevance( d_syms_quants[s][i], r+1 );
        }
      }
    }
  }
}


QuantPhaseReq::QuantPhaseReq( Node n, bool computeEq ){
  initialize( n, computeEq );
}

void QuantPhaseReq::initialize( Node n, bool computeEq ){
  std::map< Node, int > phaseReqs2;
  computePhaseReqs( n, false, phaseReqs2 );
  for( std::map< Node, int >::iterator it = phaseReqs2.begin(); it != phaseReqs2.end(); ++it ){
    if( it->second==1 ){
      d_phase_reqs[ it->first ] = true;
    }else if( it->second==-1 ){
      d_phase_reqs[ it->first ] = false;
    }
  }
  Debug("inst-engine-phase-req") << "Phase requirements for " << n << ":" << std::endl;
  //now, compute if any patterns are equality required
  if( computeEq ){
    for( std::map< Node, bool >::iterator it = d_phase_reqs.begin(); it != d_phase_reqs.end(); ++it ){
      Debug("inst-engine-phase-req") << "   " << it->first << " -> " << it->second << std::endl;
      if( it->first.getKind()==EQUAL ){
        if( quantifiers::TermDb::hasInstConstAttr(it->first[0]) ){
          if( !quantifiers::TermDb::hasInstConstAttr(it->first[1]) ){
            d_phase_reqs_equality_term[ it->first[0] ] = it->first[1];
            d_phase_reqs_equality[ it->first[0] ] = it->second;
            Debug("inst-engine-phase-req") << "      " << it->first[0] << ( it->second ? " == " : " != " ) << it->first[1] << std::endl;
          }
        }else if( quantifiers::TermDb::hasInstConstAttr(it->first[1]) ){
          d_phase_reqs_equality_term[ it->first[1] ] = it->first[0];
          d_phase_reqs_equality[ it->first[1] ] = it->second;
          Debug("inst-engine-phase-req") << "      " << it->first[1] << ( it->second ? " == " : " != " ) << it->first[0] << std::endl;
        }
      }
    }
  }
}

void QuantPhaseReq::computePhaseReqs( Node n, bool polarity, std::map< Node, int >& phaseReqs ){
  bool newReqPol = false;
  bool newPolarity;
  if( n.getKind()==NOT ){
    newReqPol = true;
    newPolarity = !polarity;
  }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }else if( n.getKind()==AND ){
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }else{
    int val = polarity ? 1 : -1;
    if( phaseReqs.find( n )==phaseReqs.end() ){
      phaseReqs[n] = val;
    }else if( val!=phaseReqs[n] ){
      phaseReqs[n] = 0;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        computePhaseReqs( n[i], !newPolarity, phaseReqs );
      }else{
        computePhaseReqs( n[i], newPolarity, phaseReqs );
      }
    }
  }
}

void QuantPhaseReq::getPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol ) {
  if( n.getKind()==AND || n.getKind()==OR || n.getKind()==SEP_STAR ){
    newHasPol = hasPol;
    newPol = pol;
  }else if( n.getKind()==IMPLIES ){
    newHasPol = hasPol;
    newPol = child==0 ? !pol : pol;
  }else if( n.getKind()==NOT ){
    newHasPol = hasPol;
    newPol = !pol;
  }else if( n.getKind()==ITE ){
    newHasPol = (child!=0) && hasPol;
    newPol = pol;
  }else if( n.getKind()==FORALL ){
    newHasPol = (child==1) && hasPol;
    newPol = pol;
  }else{
    newHasPol = false;
    newPol = pol;
  }
}

void QuantPhaseReq::getEntailPolarity( Node n, int child, bool hasPol, bool pol, bool& newHasPol, bool& newPol ) {
  if( n.getKind()==AND || n.getKind()==OR || n.getKind()==SEP_STAR ){
    newHasPol = hasPol && pol!=( n.getKind()==OR );
    newPol = pol;
  }else if( n.getKind()==IMPLIES ){
    newHasPol = hasPol && !pol;
    newPol = child==0 ? !pol : pol;
  }else if( n.getKind()==NOT ){
    newHasPol = hasPol;
    newPol = !pol;
  }else{
    newHasPol = false;
    newPol = pol;
  }
}

void QuantEPR::registerNode( Node n, std::map< int, std::map< Node, bool > >& visited, bool beneathQuant, bool hasPol, bool pol ) {
  int vindex = hasPol ? ( pol ? 1 : -1 ) : 0;
  if( visited[vindex].find( n )==visited[vindex].end() ){
    visited[vindex][n] = true;
    Trace("quant-epr-debug") << "QuantEPR::registerNode " << n << std::endl;
    if( n.getKind()==FORALL ){
      if( beneathQuant || !hasPol || !pol ){
        for( unsigned i=0; i<n[0].getNumChildren(); i++ ){
          TypeNode tn = n[0][i].getType();
          if( d_non_epr.find( tn )==d_non_epr.end() ){
            Trace("quant-epr") << "Sort " << tn << " is non-EPR because of nested or possible existential quantification." << std::endl;
            d_non_epr[tn] = true;
          }
        }
      }else{
        beneathQuant = true;
      }
    }
    TypeNode tn = n.getType();
    
    if( n.getNumChildren()>0 ){
      if( tn.isSort() ){
        if( d_non_epr.find( tn )==d_non_epr.end() ){
          Trace("quant-epr") << "Sort " << tn << " is non-EPR because of " << n << std::endl;
          d_non_epr[tn] = true;
        }
      }
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        bool newHasPol;
        bool newPol;
        QuantPhaseReq::getPolarity( n, i, hasPol, pol, newHasPol, newPol );
        registerNode( n[i], visited, beneathQuant, newHasPol, newPol );
      }
    }else if( tn.isSort() ){
      if( n.getKind()==BOUND_VARIABLE ){
        if( d_consts.find( tn )==d_consts.end() ){
          //mark that at least one constant must occur
          d_consts[tn].clear();
        }
      }else if( std::find( d_consts[tn].begin(), d_consts[tn].end(), n )==d_consts[tn].end() ){
        d_consts[tn].push_back( n );
        Trace("quant-epr") << "...constant of type " << tn << " : " << n << std::endl;
      }
    }
  }
}

void QuantEPR::registerAssertion( Node assertion ) {
  std::map< int, std::map< Node, bool > > visited;
  registerNode( assertion, visited, false, true, true );
}

void QuantEPR::finishInit() {
  Trace("quant-epr-debug") << "QuantEPR::finishInit" << std::endl;
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_consts.begin(); it != d_consts.end(); ++it ){
    Assert( d_epr_axiom.find( it->first )==d_epr_axiom.end() );
    Trace("quant-epr-debug") << "process " << it->first << std::endl;
    if( d_non_epr.find( it->first )!=d_non_epr.end() ){
      Trace("quant-epr-debug") << "...non-epr" << std::endl;
      it->second.clear();
    }else{
      Trace("quant-epr-debug") << "...epr, #consts = " << it->second.size() << std::endl;
      if( it->second.empty() ){
        it->second.push_back( NodeManager::currentNM()->mkSkolem( "e", it->first, "EPR base constant" ) );
      }
      if( Trace.isOn("quant-epr") ){
        Trace("quant-epr") << "Type " << it->first << " is EPR, with constants : " << std::endl;
        for( unsigned i=0; i<it->second.size(); i++ ){
          Trace("quant-epr") << "  " << it->second[i] << std::endl;
        }
      }
    }
  }
}

bool QuantEPR::isEPRConstant( TypeNode tn, Node k ) {
  return std::find( d_consts[tn].begin(), d_consts[tn].end(), k )!=d_consts[tn].end();
}

void QuantEPR::addEPRConstant( TypeNode tn, Node k ) {
  Assert( isEPR( tn ) );
  Assert( d_epr_axiom.find( tn )==d_epr_axiom.end() );
  if( !isEPRConstant( tn, k ) ){
    d_consts[tn].push_back( k );
  }
}

Node QuantEPR::mkEPRAxiom( TypeNode tn ) {
  Assert( isEPR( tn ) );
  std::map< TypeNode, Node >::iterator ita = d_epr_axiom.find( tn );
  if( ita==d_epr_axiom.end() ){
    std::vector< Node > disj;
    Node x = NodeManager::currentNM()->mkBoundVar( tn );
    for( unsigned i=0; i<d_consts[tn].size(); i++ ){
      disj.push_back( NodeManager::currentNM()->mkNode( tn.isBoolean() ? IFF : EQUAL, x, d_consts[tn][i] ) );
    }
    Assert( !disj.empty() );
    d_epr_axiom[tn] = NodeManager::currentNM()->mkNode( FORALL, NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, x ), disj.size()==1 ? disj[0] : NodeManager::currentNM()->mkNode( OR, disj ) );
    return d_epr_axiom[tn];
  }else{
    return ita->second;
  }
}


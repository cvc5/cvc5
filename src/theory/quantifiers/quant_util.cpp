/*********************                                                        */
/*! \file quant_util.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
  if ( n.getKind()==MULT ){
    if( n.getNumChildren()==2 && msum.find(n[1])==msum.end() && n[0].isConst() ){
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
      if( lit[1].isConst() ){
        if( !lit[1].getConst<Rational>().isZero() ){
          msum[Node::null()] = negate( lit[1] );
        }
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
              msum[it->first] = negate( it->second.isNull() ? NodeManager::currentNM()->mkConst( Rational(1) ) : it->second );
            }
          }
          return true;
        }
      }
    }
  }
  return false;
}

int QuantArith::isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k, bool doCoeff ) {
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
      veq = children.size()>1 ? NodeManager::currentNM()->mkNode( PLUS, children ) :
                                (children.size()==1 ? children[0] : NodeManager::currentNM()->mkConst( Rational(0) ));
      Node vc = v;
      if( !r.isOne() && !r.isNegativeOne() ){
        if( doCoeff ){
          vc = NodeManager::currentNM()->mkNode( MULT, NodeManager::currentNM()->mkConst( r.abs() ), vc );
        }else{
          return 0;
        }
      }
      if( r.sgn()==1 ){
        veq = negate(veq);
      }
      veq = Rewriter::rewrite( veq );
      bool inOrder = r.sgn()==1 || k==EQUAL;
      veq = NodeManager::currentNM()->mkNode( k, inOrder ? vc : veq, inOrder ? veq : vc );
      return inOrder ? 1 : -1;
    }
  }
  return 0;
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

bool QuantArith::solveEqualityFor( Node lit, Node v, Node & veq ) {
  Assert( lit.getKind()==EQUAL || lit.getKind()==IFF );
  //first look directly at sides
  TypeNode tn = lit[0].getType();
  for( unsigned r=0; r<2; r++ ){
    if( lit[r]==v ){
      Node olitr = lit[r==0 ? 1 : 0];
      veq = tn.isBoolean() ? lit[r].iffNode( olitr ) : lit[r].eqNode( olitr );
      return true;
    }
  }
  if( tn.isInteger() || tn.isReal() ){
    std::map< Node, Node > msum;
    if( QuantArith::getMonomialSumLit( lit, msum ) ){
      if( QuantArith::isolate( v, msum, veq, EQUAL ) ){
        if( veq[0]!=v ){
          Assert( veq[1]==v );
          veq = v.eqNode( veq[0] );
        }
        return true;
      }
    }
  }
  return false;
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
  Assert( n.getKind()!=IMPLIES && n.getKind()!=XOR );
  newHasPol = hasPol;
  newPol = pol;
  if( n.getKind()==NOT ){
    newPol = !pol;
  }else if( n.getKind()==IFF ){
    newHasPol = false;
  }else if( n.getKind()==ITE ){
    if( child==0 ){
      newHasPol = false;
    }
  }
}

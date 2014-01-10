/*********************                                                        */
/*! \file quant_util.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of quantifier utilities
 **/

#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;


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
      }
    }
  }
  return false;
}

bool QuantArith::isolate( Node v, std::map< Node, Node >& msum, Node & veq, Kind k ) {
  if( msum.find(v)!=msum.end() ){
    std::vector< Node > children;
    Rational r = msum[v].isNull() ? Rational(1) : msum[v].getConst<Rational>();
    if ( r.sgn()!=0 ){
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        if( it->first.isNull() || it->first!=v ){
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
      if( !r.isNegativeOne() ){
        if( r.isOne() ){
          veq = negate(veq);
        }else{
          //TODO
          return false;
        }
      }
      veq = Rewriter::rewrite( veq );
      veq = NodeManager::currentNM()->mkNode( k, r.sgn()==1 ? v : veq, r.sgn()==1 ? veq : v );
      return true;
    }
    return false;
  }else{
    return false;
  }
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
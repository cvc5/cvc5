/*********************                                                        */
/*! \file bounded_integers.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Bounded integers module
 **
 ** This class manages integer bounds for quantifiers
 **/

#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/quantifiers/first_order_model.h"

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

void BoundedIntegers::RangeModel::initialize() {
  //add initial split lemma
  Node ltr = NodeManager::currentNM()->mkNode( LT, d_range, NodeManager::currentNM()->mkConst( Rational(0) ) );
  ltr = Rewriter::rewrite( ltr );
  Trace("bound-integers-lemma") << " *** bound int: initial split on " << ltr << std::endl;
  d_bi->getQuantifiersEngine()->getOutputChannel().split( ltr );
  Node ltr_lit = ltr.getKind()==NOT ? ltr[0] : ltr;
  d_range_literal[-1] = ltr_lit;
  d_lit_to_range[ltr_lit] = -1;
  d_lit_to_pol[ltr_lit] = ltr.getKind()!=NOT;
  //register with bounded integers
  Trace("bound-integers-debug") << "Literal " << ltr_lit << " is literal for " << d_range << std::endl;
  d_bi->addLiteralFromRange(ltr_lit, d_range);
}

void BoundedIntegers::RangeModel::assertNode(Node n) {
  bool pol = n.getKind()!=NOT;
  Node nlit = n.getKind()==NOT ? n[0] : n;
  if( d_lit_to_range.find( nlit )!=d_lit_to_range.end() ){
    Trace("bound-integers-assert") << "With polarity = " << pol << " (req "<< d_lit_to_pol[nlit] << ")";
    Trace("bound-integers-assert") << ", found literal " << nlit;
    Trace("bound-integers-assert") << ", it is bound literal " << d_lit_to_range[nlit] << " for " << d_range << std::endl;
    d_range_assertions[nlit] = (pol==d_lit_to_pol[nlit]);
    if( pol!=d_lit_to_pol[nlit] ){
      //check if we need a new split?
      if( !d_has_range ){
        bool needsRange = true;
        for( std::map< Node, int >::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
          if( d_range_assertions.find( it->first )==d_range_assertions.end() ){
            needsRange = false;
            break;
          }
        }
        if( needsRange ){
          allocateRange();
        }
      }
    }else{
      if (!d_has_range || d_lit_to_range[nlit]<d_curr_range ){
        Trace("bound-integers-bound") << "Successfully bound " << d_range << " to " << d_lit_to_range[nlit] << std::endl;
        d_curr_range = d_lit_to_range[nlit];
      }
      //set the range
      d_has_range = true;
    }
  }else{
    Message() << "Could not find literal " << nlit << " for range " << d_range << std::endl;
    exit(0);
  }
}

void BoundedIntegers::RangeModel::allocateRange() {
  d_curr_max++;
  int newBound = d_curr_max;
  Trace("bound-integers-proc") << "Allocate range bound " << newBound << " for " << d_range << std::endl;
  //TODO: newBound should be chosen in a smarter way
  Node ltr = NodeManager::currentNM()->mkNode( LEQ, d_range, NodeManager::currentNM()->mkConst( Rational(newBound) ) );
  ltr = Rewriter::rewrite( ltr );
  Trace("bound-integers-lemma") << " *** bound int: split on " << ltr << std::endl;
  d_bi->getQuantifiersEngine()->getOutputChannel().split( ltr );
  Node ltr_lit = ltr.getKind()==NOT ? ltr[0] : ltr;
  d_range_literal[newBound] = ltr_lit;
  d_lit_to_range[ltr_lit] = newBound;
  d_lit_to_pol[ltr_lit] = ltr.getKind()!=NOT;
  //register with bounded integers
  d_bi->addLiteralFromRange(ltr_lit, d_range);
}

Node BoundedIntegers::RangeModel::getNextDecisionRequest() {
  //request the current cardinality as a decision literal, if not already asserted
  for( std::map< Node, int >::iterator it = d_lit_to_range.begin(); it != d_lit_to_range.end(); ++it ){
    int i = it->second;
    if( !d_has_range || i<d_curr_range ){
      Node rn = it->first;
      Assert( !rn.isNull() );
      if( d_range_assertions.find( rn )==d_range_assertions.end() ){
        if (!d_lit_to_pol[it->first]) {
          rn = rn.negate();
        }
        Trace("bound-integers-dec") << "For " << d_range << ", make decision " << rn << " to make range " << i << std::endl;
        return rn;
      }
    }
  }
  return Node::null();
}


BoundedIntegers::BoundedIntegers(context::Context* c, QuantifiersEngine* qe) :
QuantifiersModule(qe), d_assertions(c){

}

bool BoundedIntegers::isBound( Node f, Node v ) {
  return std::find( d_set[f].begin(), d_set[f].end(), v )!=d_set[f].end();
}

bool BoundedIntegers::hasNonBoundVar( Node f, Node b ) {
  if( b.getKind()==BOUND_VARIABLE ){
    if( isBound( f, b ) ){
      return true;
    }
  }else{
    for( unsigned i=0; i<b.getNumChildren(); i++ ){
      if( hasNonBoundVar( f, b[i] ) ){
        return true;
      }
    }
  }
  return false;
}

void BoundedIntegers::processLiteral( Node f, Node lit, bool pol ) {
  if( lit.getKind()==GEQ && lit[0].getType().isInteger() ){
    std::map< Node, Node > msum;
    if (QuantArith::getMonomialSumLit( lit, msum )){
      Trace("bound-integers-debug") << "Literal (polarity = " << pol << ") " << lit << " is monomial sum : " << std::endl;
      for(std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        Trace("bound-integers-debug") << "  ";
        if( !it->second.isNull() ){
          Trace("bound-integers-debug") << it->second;
          if( !it->first.isNull() ){
            Trace("bound-integers-debug") << " * ";
          }
        }
        if( !it->first.isNull() ){
          Trace("bound-integers-debug") << it->first;
        }
        Trace("bound-integers-debug") << std::endl;
      }
      Trace("bound-integers-debug") << std::endl;
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        if ( !it->first.isNull() && it->first.getKind()==BOUND_VARIABLE ){
          Node veq;
          if( QuantArith::isolate( it->first, msum, veq, GEQ ) ){
            Node n1 = veq[0];
            Node n2 = veq[1];
            if(pol){
              //flip
              n1 = veq[1];
              n2 = veq[0];
              if( n1.getKind()==BOUND_VARIABLE ){
                n2 = QuantArith::offset( n2, 1 );
              }else{
                n1 = QuantArith::offset( n1, -1 );
              }
              veq = NodeManager::currentNM()->mkNode( GEQ, n1, n2 );
            }
            Trace("bound-integers-debug") << "Isolated for " << it->first << " : (" << n1 << " >= " << n2 << ")" << std::endl;
            Node bv = n1.getKind()==BOUND_VARIABLE ? n1 : n2;
            if( !isBound( f, bv ) ){
              if( !hasNonBoundVar( f, n1.getKind()==BOUND_VARIABLE ? n2 : n1 ) ) {
                Trace("bound-integers-debug") << "The bound is relevant." << std::endl;
                d_bounds[n1.getKind()==BOUND_VARIABLE ? 0 : 1][f][bv] = (n1.getKind()==BOUND_VARIABLE ? n2 : n1);
              }
            }
          }
        }
      }
    }
  }else if( lit.getKind()==LEQ || lit.getKind()==LT || lit.getKind()==GT ) {
    std::cout << "BoundedIntegers : Bad kind for literal : " << lit << std::endl;
    exit(0);
  }
}

void BoundedIntegers::process( Node f, Node n, bool pol ){
  if( (( n.getKind()==IMPLIES || n.getKind()==OR) && pol) || (n.getKind()==AND && !pol) ){
    for( unsigned i=0; i<n.getNumChildren(); i++) {
      bool newPol = n.getKind()==IMPLIES && i==0 ? !pol : pol;
      process( f, n[i], newPol );
    }
  }else if( n.getKind()==NOT ){
    process( f, n[0], !pol );
  }else {
    processLiteral( f, n, pol );
  }
}

void BoundedIntegers::check( Theory::Effort e ) {

}


void BoundedIntegers::addLiteralFromRange( Node lit, Node r ) {
  d_lit_to_ranges[lit].push_back(r);
  //check if it is already asserted?
  if(d_assertions.find(lit)!=d_assertions.end()){
    d_rms[r]->assertNode( d_assertions[lit] ? lit : lit.negate() );
  }
}

void BoundedIntegers::registerQuantifier( Node f ) {
  Trace("bound-integers") << "Register quantifier " << f << std::endl;
  bool hasIntType = false;
  for( unsigned i=0; i<f[0].getNumChildren(); i++) {
    if( f[0][i].getType().isInteger() ){
      hasIntType = true;
      break;
    }
  }
  if( hasIntType ){
    bool success;
    do{
      success = false;
      process( f, f[1], true );
      for( std::map< Node, Node >::iterator it = d_bounds[0][f].begin(); it != d_bounds[0][f].end(); ++it ){
        Node v = it->first;
        if( !isBound(f,v) ){
          if( d_bounds[1][f].find(v)!=d_bounds[1][f].end() ){
            d_set[f].push_back(v);
            success = true;
          }
        }
      }
    }while( success );
    Trace("bound-integers") << "Bounds are : " << std::endl;
    for( unsigned i=0; i<d_set[f].size(); i++) {
      Node v = d_set[f][i];
      Node r = NodeManager::currentNM()->mkNode( MINUS, d_bounds[1][f][v], d_bounds[0][f][v] );
      d_range[f][v] = Rewriter::rewrite( r );
      Trace("bound-integers") << "  " << d_bounds[0][f][v] << " <= " << v << " <= " << d_bounds[1][f][v] << " (range is " << d_range[f][v] << ")" << std::endl;
    }
    if( d_set[f].size()==f[0].getNumChildren() ){
      d_bound_quants.push_back( f );
      for( unsigned i=0; i<d_set[f].size(); i++) {
        Node v = d_set[f][i];
        Node r = d_range[f][v];
        if( std::find(d_ranges.begin(), d_ranges.end(), r)==d_ranges.end() ){
          d_ranges.push_back( r );
          d_rms[r] = new RangeModel(this, r, d_quantEngine->getSatContext() );
          d_rms[r]->initialize();
        }
      }
    }
  }
}

void BoundedIntegers::assertNode( Node n ) {
  Trace("bound-integers-assert") << "Assert " << n << std::endl;
  Node nlit = n.getKind()==NOT ? n[0] : n;
  if( d_lit_to_ranges.find(nlit)!=d_lit_to_ranges.end() ){
    Trace("bound-integers-assert") << "This is the bounding literal for " << d_lit_to_ranges[nlit].size() << " ranges." << std::endl;
    for( unsigned i=0; i<d_lit_to_ranges[nlit].size(); i++) {
      Node r = d_lit_to_ranges[nlit][i];
      Trace("bound-integers-assert") << "  ...this is a bounding literal for " << r << std::endl;
      d_rms[r]->assertNode( n );
    }
  }
  d_assertions[nlit] = n.getKind()!=NOT;
}

Node BoundedIntegers::getNextDecisionRequest() {
  Trace("bound-integers-dec") << "bi: Get next decision request?" << std::endl;
  for( unsigned i=0; i<d_ranges.size(); i++) {
    Node d = d_rms[d_ranges[i]]->getNextDecisionRequest();
    if (!d.isNull()) {
      return d;
    }
  }
  return Node::null();
}


Node BoundedIntegers::getValueInModel( Node n ) {
  return d_quantEngine->getModel()->getValue( n );
}
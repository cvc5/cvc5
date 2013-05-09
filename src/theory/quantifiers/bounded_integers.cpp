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

using namespace CVC4;
using namespace std;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::kind;

BoundedIntegers::BoundedIntegers(QuantifiersEngine* qe) : QuantifiersModule(qe){

}

void BoundedIntegers::processLiteral( Node f, Node lit, bool pol ) {
  if( lit.getKind()==GEQ && lit[0].getType().isInteger() ){
    std::map< Node, Node > msum;
    if (QuantArith::getMonomialSumLit( lit, msum )){
      Trace("bound-integers") << "Literal " << lit << " is monomial sum : " << std::endl;
      for(std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        Trace("bound-integers") << "  ";
        if( !it->second.isNull() ){
          Trace("bound-integers") << it->second;
          if( !it->first.isNull() ){
            Trace("bound-integers") << " * ";
          }
        }
        if( !it->first.isNull() ){
          Trace("bound-integers") << it->first;
        }
        Trace("bound-integers") << std::endl;
      }
      Trace("bound-integers") << std::endl;
      for( std::map< Node, Node >::iterator it = msum.begin(); it != msum.end(); ++it ){
        if ( !it->first.isNull() && it->first.getKind()==BOUND_VARIABLE ){
          Node veq;
          if( QuantArith::isolate( it->first, msum, veq, GEQ ) ){
            Trace("bound-integers") << "Isolated for " << it->first << " : " << veq << std::endl;
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

void BoundedIntegers::registerQuantifier( Node f ) {
  bool hasIntType = false;
  for( unsigned i=0; i<f[0].getNumChildren(); i++) {
    if( f[0][i].getType().isInteger() ){
      hasIntType = true;
      break;
    }
  }
  if( hasIntType ){
    process( f, f[1], true );
  }
}

void BoundedIntegers::assertNode( Node n ) {

}

Node BoundedIntegers::getNextDecisionRequest() {
  return Node::null();
}

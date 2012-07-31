/*********************                                                        */
/*! \file theory_arrays_instantiator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory_arrays_instantiator class
 **/

#include "theory/theory_engine.h"
#include "theory/arrays/theory_arrays_instantiator.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/quantifiers/options.h"
#include "theory/rr_candidate_generator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;

InstantiatorTheoryArrays::InstantiatorTheoryArrays(context::Context* c, QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryArrays::preRegisterTerm( Node t ){

}

void InstantiatorTheoryArrays::assertNode( Node assertion ){
  Debug("quant-arrays-assert") << "InstantiatorTheoryArrays::assertNode: " << assertion << std::endl;
  d_quantEngine->addTermToDatabase( assertion );
  if( options::cbqi() ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}


void InstantiatorTheoryArrays::processResetInstantiationRound( Theory::Effort effort ){

}

int InstantiatorTheoryArrays::process( Node f, Theory::Effort effort, int e ){
  return InstStrategy::STATUS_SAT;
}

bool InstantiatorTheoryArrays::hasTerm( Node a ){
  return ((TheoryArrays*)d_th)->getEqualityEngine()->hasTerm( a );
}

bool InstantiatorTheoryArrays::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return ((TheoryArrays*)d_th)->getEqualityEngine()->areEqual( a, b );
  }else{
    return false;
  }
}

bool InstantiatorTheoryArrays::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else if( hasTerm( a ) && hasTerm( b ) ){
    return ((TheoryArrays*)d_th)->getEqualityEngine()->areDisequal( a, b, false );
  }else{
    return false;
  }
}

Node InstantiatorTheoryArrays::getRepresentative( Node a ){
  if( hasTerm( a ) ){
    return ((TheoryArrays*)d_th)->getEqualityEngine()->getRepresentative( a );
  }else{
    return a;
  }
}

eq::EqualityEngine* InstantiatorTheoryArrays::getEqualityEngine(){
  return ((TheoryArrays*)d_th)->getEqualityEngine();
}

void InstantiatorTheoryArrays::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  if( hasTerm( a ) ){
    a = getEqualityEngine()->getRepresentative( a );
    eq::EqClassIterator eqc_iter( a, getEqualityEngine() );
    while( !eqc_iter.isFinished() ){
      if( std::find( eqc.begin(), eqc.end(), *eqc_iter )==eqc.end() ){
        eqc.push_back( *eqc_iter );
      }
      eqc_iter++;
    }
  }
}

rrinst::CandidateGenerator* InstantiatorTheoryArrays::getRRCanGenClasses(){
  arrays::TheoryArrays* ar = static_cast<arrays::TheoryArrays *>(getTheory());
  eq::EqualityEngine* ee =
    static_cast<eq::EqualityEngine*>(ar->getEqualityEngine());
  return new eq::rrinst::CandidateGeneratorTheoryEeClasses(ee);
}

rrinst::CandidateGenerator* InstantiatorTheoryArrays::getRRCanGenClass(){
  arrays::TheoryArrays* ar = static_cast<arrays::TheoryArrays *>(getTheory());
  eq::EqualityEngine* ee =
    static_cast<eq::EqualityEngine*>(ar->getEqualityEngine());
  return new eq::rrinst::CandidateGeneratorTheoryEeClass(ee);
}

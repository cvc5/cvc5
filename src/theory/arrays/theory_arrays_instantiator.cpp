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
  if( Options::current()->cbqi ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      setHasConstraintsFrom( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}


void InstantiatorTheoryArrays::processResetInstantiationRound( Theory::Effort effort ){

}

int InstantiatorTheoryArrays::process( Node f, Theory::Effort effort, int e, int limitInst ){
  return InstStrategy::STATUS_SAT;
}

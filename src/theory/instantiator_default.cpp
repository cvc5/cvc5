/*********************                                                        */
/*! \file instantiator_default.cpp
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
 ** \brief Implementation of instantiator_default class
 **/

#include "theory/instantiator_default.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;

InstantiatorDefault::InstantiatorDefault(context::Context* c, QuantifiersEngine* ie, Theory* th) :
  Instantiator( c, ie, th ) {
}

void InstantiatorDefault::assertNode( Node assertion ){
}

void InstantiatorDefault::processResetInstantiationRound( Theory::Effort effort ){
}

int InstantiatorDefault::process( Node f, Theory::Effort effort, int e, int limitInst ){
  if( e < 4 ){
    return InstStrategy::STATUS_UNFINISHED;
  }else if( e == 4 ){
    Debug("quant-default") << "Process " << f << " : " << std::endl;
    InstMatch m;
    for( int j=0; j<(int)d_quantEngine->getNumInstantiationConstants( f ); j++ ){
      Node i = d_quantEngine->getInstantiationConstant( f, j );
      Debug("quant-default") << "Getting value for " << i << std::endl;
      if( d_quantEngine->getTheoryEngine()->theoryOf( i )==getTheory() ){    //if it belongs to this theory
        Node val = d_th->getValue( i );
        Debug("quant-default") << "Default Instantiate for " << d_th->getId() << ", setting " << i << " = " << val << std::endl;
        m.d_map[ i ] = val;
      }
    }
    d_quantEngine->addInstantiation( f, m );
  }
  return InstStrategy::STATUS_UNKNOWN;
}

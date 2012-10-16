/*********************                                                        */
/*! \file theory_quantifiers_instantiator.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory_quantifiers_instantiator class
 **/

#include "theory/quantifiers/theory_quantifiers_instantiator.h"
#include "theory/quantifiers/theory_quantifiers.h"
#include "theory/quantifiers/options.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

InstantiatorTheoryQuantifiers::InstantiatorTheoryQuantifiers(context::Context* c, QuantifiersEngine* ie, Theory* th) :
Instantiator( c, ie, th ){

}

void InstantiatorTheoryQuantifiers::assertNode( Node assertion ){
  Debug("quant-quant-assert") << "InstantiatorTheoryQuantifiers::check: " << assertion << std::endl;
  if( options::cbqi() ){
    if( assertion.hasAttribute(InstConstantAttribute()) ){
      Debug("quant-quant-assert") << "   -> has constraints from " << assertion.getAttribute(InstConstantAttribute()) << std::endl;
      setQuantifierActive( assertion.getAttribute(InstConstantAttribute()) );
    }else if( assertion.getKind()==NOT && assertion[0].hasAttribute(InstConstantAttribute()) ){
      Debug("quant-quant-assert") << "   -> has constraints from " << assertion[0].getAttribute(InstConstantAttribute()) << std::endl;
      setQuantifierActive( assertion[0].getAttribute(InstConstantAttribute()) );
    }
  }
}

void InstantiatorTheoryQuantifiers::processResetInstantiationRound( Theory::Effort effort ){

}


int InstantiatorTheoryQuantifiers::process( Node f, Theory::Effort effort, int e ){
  Debug("quant-quant") << "Quant: Try to solve (" << e << ") for " << f << "... " << std::endl;
  if( e<5 ){
    return InstStrategy::STATUS_UNFINISHED;
  }else if( e==5 ){
    //add random addition
    InstMatch m;
    if( d_quantEngine->addInstantiation( f, m ) ){
      ++(d_statistics.d_instantiations);
    }
  }
  return InstStrategy::STATUS_UNKNOWN;
}

InstantiatorTheoryQuantifiers::Statistics::Statistics():
  d_instantiations("InstantiatorTheoryQuantifiers::Instantiations_Total", 0)
{
  StatisticsRegistry::registerStat(&d_instantiations);
}

InstantiatorTheoryQuantifiers::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_instantiations);
}


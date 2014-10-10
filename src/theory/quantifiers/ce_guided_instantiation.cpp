/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **
 **/

#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/first_order_model.h"

using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace std;

namespace CVC4 {

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ) {

  
}

void CegInstantiation::check( Theory::Effort e, unsigned quant_e ) {
  //TODO
}

void CegInstantiation::registerQuantifier( Node q ) {
  //TODO
}

void CegInstantiation::assertNode( Node n ) {
  
}
  
}
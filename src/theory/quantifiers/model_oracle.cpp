/*********************                                                        */
/*! \file model_oracle.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model_oracle
 **/

#include "theory/quantifiers/model_oracle.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {
  
ModelOracle::ModelOracle( QuantifiersEngine * qe ) : QuantifiersModule(qe) 
{

}

bool ModelOracle::needsCheck(Theory::Effort e) 
{
  return e >= Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort ModelOracle::needsModel(Theory::Effort e)
{
  return QEFFORT_MODEL; 
}
  
void ModelOracle::check(Theory::Effort e, QEffort quant_e)
{
  if( e!=Theory::EFFORT_LAST_CALL || quant_e != QEFFORT_MODEL )
  {
    return;
  }
  // see if the negation of each quantified formula is satisfiable in the model
  std::vector< Node > disj;
  TheoryModel * tm = d_quantEngine->getModel();
  for( unsigned i=0, nquant = tm->getNumAssertedQuantifiers(); i<nuant; i++ )
  {
    Node q = d_quantEngine->getModel()->getAssertedQuantifier( i );
    d_quantEngine->getSkolemize()->getSkolemizedBody(q);
    disj.push_back(q);
  }
}
  
} /* CVC4::theory::quantifiers namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */

/*********************                                                        */
/*! \file quantifiers_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The quantifiers registry
 **/

#include "theory/quantifiers/quantifiers_registry.h"

#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantifiersModule * QuantifiersRegistry::getOwner( Node q ) const {
  std::map< Node, QuantifiersModule * >::const_iterator it = d_owner.find( q );
  if( it==d_owner.end() ){
    return nullptr;
  }
  return it->second;
}

void QuantifiersRegistry::setOwner( Node q, QuantifiersModule * m, int32_t priority ) {
  QuantifiersModule * mo = getOwner( q );
  if( mo==m ){
    return;
  }
  if( mo!=nullptr ){
    if( priority<=d_owner_priority[q] ){
      Trace("quant-warn") << "WARNING: setting owner of " << q << " to " << ( m ? m->identify() : "null" ) << ", but already has owner " << mo->identify() << " with higher priority!" << std::endl;
      return;
    }
  }
  d_owner[q] = m;
  d_owner_priority[q] = priority;
  
}
/*
void QuantifiersRegistry::setOwner(Node q, quantifiers::QAttributes& qa)
{
  if (qa.d_sygus || (options::sygusRecFun() && !qa.d_fundef_f.isNull()))
  {
    if (d_qmodules->d_synth_e.get() == nullptr)
    {
      Trace("quant-warn") << "WARNING : synth engine is null, and we have : "
                          << q << std::endl;
    }
    // set synth engine as owner since this is either a conjecture or a function
    // definition to be used by sygus
    setOwner(q, d_qmodules->d_synth_e.get(), 2);
  }
}
*/

bool QuantifiersRegistry::hasOwnership( Node q, QuantifiersModule * m ) const {
  QuantifiersModule * mo = getOwner( q );
  return mo==m || mo==nullptr;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

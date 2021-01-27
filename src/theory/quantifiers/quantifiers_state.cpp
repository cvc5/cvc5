/*********************                                                        */
/*! \file quantifiers_state.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for quantifiers state
 **/

#include "theory/quantifiers/quantifiers_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantifiersState::QuantifiersState(context::Context* c,
                                   context::UserContext* u,
                                   Valuation val)
    : TheoryState(c, u, val)
{
}

void QuantifiersState::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  if( d_ee->hasTerm( a ) ){
    Node rep = d_ee->getRepresentative( a );
    eq::EqClassIterator eqc_iter( rep, d_ee );
    while( !eqc_iter.isFinished() ){
      eqc.push_back( *eqc_iter );
      eqc_iter++;
    }
  }else{
    eqc.push_back( a );
  }
  //a should be in its equivalence class
  Assert(std::find(eqc.begin(), eqc.end(), a) != eqc.end());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

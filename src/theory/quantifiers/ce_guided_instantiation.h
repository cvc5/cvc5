/*********************                                                        */
/*! \file ce_guided_instantiation.h
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
 **/

#include "cvc4_private.h"

#ifndef CE_GUIDED_INSTANTIATION_H
#define CE_GUIDED_INSTANTIATION_H

#include "context/cdhashmap.h"
#include "context/cdchunk_list.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class CegInstantiation : public QuantifiersModule
{
public:
  CegInstantiation( QuantifiersEngine * qe, context::Context* c );
public:
  /* Call during quantifier engine's check */
  void check( Theory::Effort e, unsigned quant_e );
  /* Called for new quantifiers */
  void registerQuantifier( Node q );
  void assertNode( Node n );
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const { return "CegInstantiation"; }
};

}
}
}

#endif

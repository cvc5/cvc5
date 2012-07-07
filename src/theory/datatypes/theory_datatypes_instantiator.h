/*********************                                                        */
/*! \file theory_datatypes_instantiator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_datatypes_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__INSTANTIATOR_DATATYPES_H
#define __CVC4__INSTANTIATOR_DATATYPES_H

#include "theory/quantifiers_engine.h"

#include "util/stats.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class InstantiatorTheoryDatatypes : public Instantiator{
  friend class QuantifiersEngine;
public:
  InstantiatorTheoryDatatypes(context::Context* c, QuantifiersEngine* ie, Theory* th);
  ~InstantiatorTheoryDatatypes() {}

  /** assertNode function, assertion is asserted to theory */
  void assertNode( Node assertion );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryDatatypes"); }
private:
  /**  reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process at effort */
  int process( Node f, Theory::Effort effort, int e, int limitInst );
  /** get value for */
  Node getValueFor( Node n );
  /** get representative */
  Node getRepresentative( Node n );

  class Statistics {
  public:
    IntStat d_instantiations;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class InstantiatiorTheoryDatatypes  */

}
}
}

#endif
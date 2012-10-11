/*********************                                                        */
/*! \file theory_quantifiers_instantiator.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_quantifiers_instantiator
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_INSTANTIATOR_H
#define __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_INSTANTIATOR_H

#include "theory/quantifiers_engine.h"

#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class InstantiatorTheoryQuantifiers : public Instantiator{
  friend class QuantifiersEngine;
public:
  InstantiatorTheoryQuantifiers(context::Context* c, QuantifiersEngine* ie, Theory* th);
  ~InstantiatorTheoryQuantifiers() {}

  /** check function, assertion is asserted to theory */
  void assertNode( Node assertion );
  /** identify */
  std::string identify() const { return std::string("InstantiatorTheoryQuantifiers"); }
private:
  /**  reset instantiation */
  void processResetInstantiationRound( Theory::Effort effort );
  /** process at effort */
  int process( Node f, Theory::Effort effort, int e );

  class Statistics {
  public:
    IntStat d_instantiations;
    Statistics();
    ~Statistics();
  };
  Statistics d_statistics;
};/* class InstantiatiorTheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_INSTANTIATOR_H */

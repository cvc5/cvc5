/*********************                                                        */
/*! \file instantiator_default.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief instantiator_default
 **/


#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INSTANTIATOR_DEFAULT_H
#define __CVC4__THEORY__QUANTIFIERS__INSTANTIATOR_DEFAULT_H

#include <string>
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {

class InstantiatorDefault : public Instantiator {
  friend class QuantifiersEngine;
protected:
  /** reset instantiation round */
  void processResetInstantiationRound(Theory::Effort effort);
  /** process quantifier */
  int process( Node f, Theory::Effort effort, int e );
public:
  InstantiatorDefault(context::Context* c, QuantifiersEngine* ie, Theory* th);
  ~InstantiatorDefault() { }
  /** check function, assertion is asserted to theory */
  void assertNode( Node assertion );
  /** identify */
  std::string identify() const { return std::string("InstantiatorDefault"); }
};/* class InstantiatorDefault */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__INSTANTIATOR_DEFAULT_H */

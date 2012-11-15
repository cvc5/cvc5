/*********************                                                        */
/*! \file theory_bool.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): ajreynol, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The theory of booleans
 **
 ** The theory of booleans.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H
#define __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H

#include "theory/theory.h"
#include "context/context.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBool : public Theory {
public:
  TheoryBool(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe) :
    Theory(THEORY_BOOL, c, u, out, valuation, logicInfo, qe) {
  }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  std::string identify() const { return std::string("TheoryBool"); }
};/* class TheoryBool */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H */

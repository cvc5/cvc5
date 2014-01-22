/*********************                                                        */
/*! \file theory_bool.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
  TheoryBool(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo) :
    Theory(THEORY_BOOL, c, u, out, valuation, logicInfo) {
  }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions);

  std::string identify() const { return std::string("TheoryBool"); }
};/* class TheoryBool */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__BOOLEANS__THEORY_BOOL_H */

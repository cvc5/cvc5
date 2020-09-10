/*********************                                                        */
/*! \file theory_bool.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory of booleans
 **
 ** The theory of booleans.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BOOLEANS__THEORY_BOOL_H
#define CVC4__THEORY__BOOLEANS__THEORY_BOOL_H

#include "context/context.h"
#include "theory/booleans/theory_bool_rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace booleans {

class TheoryBool : public Theory {
 public:
  TheoryBool(context::Context* c,
             context::UserContext* u,
             OutputChannel& out,
             Valuation valuation,
             const LogicInfo& logicInfo);

  TheoryRewriter* getTheoryRewriter() override { return &d_rewriter; }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;

  //void check(Effort);

  std::string identify() const override { return std::string("TheoryBool"); }

 private:
  /** The theory rewriter for this theory. */
  TheoryBoolRewriter d_rewriter;
};/* class TheoryBool */

}/* CVC4::theory::booleans namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__BOOLEANS__THEORY_BOOL_H */

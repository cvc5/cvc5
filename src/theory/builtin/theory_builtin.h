/*********************                                                        */
/*! \file theory_builtin.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Built-in theory.
 **
 ** Built-in theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H
#define CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H

#include "theory/builtin/theory_builtin_rewriter.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace builtin {

class TheoryBuiltin : public Theory
{
 public:
  TheoryBuiltin(context::Context* c,
                context::UserContext* u,
                OutputChannel& out,
                Valuation valuation,
                const LogicInfo& logicInfo);

  TheoryRewriter* getTheoryRewriter() override { return &d_rewriter; }

  std::string identify() const override;

  /** finish initialization */
  void finishInit() override;

 private:
  /** The theory rewriter for this theory. */
  TheoryBuiltinRewriter d_rewriter;
}; /* class TheoryBuiltin */

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BUILTIN__THEORY_BUILTIN_H */

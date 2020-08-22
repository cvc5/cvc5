/*********************                                                        */
/*! \file quantifiers_state.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for quantifiers state
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H
#define CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H

#include "theory/theory_state.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/**
 * The quantifiers state.
 */
class QuantifiersState : public TheoryState
{
 public:
  QuantifiersState(context::Context* c, context::UserContext* u, Valuation val);
  ~QuantifiersState() {}
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_STATE_H */

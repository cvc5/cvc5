/*********************                                                        */
/*! \file decision_attributes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriter attributes
 **
 ** Rewriter attributes.
 **/

#include "cvc4_private.h"

#ifndef CVC4__DECISION__DECISION_ATTRIBUTES_H
#define CVC4__DECISION__DECISION_ATTRIBUTES_H

#include "options/decision_weight.h"
#include "expr/attribute.h"

namespace cvc5 {
namespace decision {
namespace attr {
  struct DecisionWeightTag {};
  }  // namespace attr

typedef expr::Attribute<attr::DecisionWeightTag, DecisionWeight> DecisionWeightAttr;

}  // namespace decision
}  // namespace cvc5

#endif /* CVC4__DECISION__DECISION_ATTRIBUTES_H */

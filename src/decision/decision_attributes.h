/*********************                                                        */
/*! \file decision_attributes.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter attributes
 **
 ** Rewriter attributes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__DECISION__DECISION_ATTRIBUTES_H
#define __CVC4__DECISION__DECISION_ATTRIBUTES_H

#include "options/decision_weight.h"
#include "expr/attribute.h"

namespace CVC4 {
namespace decision {
namespace attr {
  struct DecisionWeightTag {};
}/* CVC4::decision::attr namespace */

typedef expr::Attribute<attr::DecisionWeightTag, DecisionWeight> DecisionWeightAttr;

}/* CVC4::decision namespace */
}/* CVC4 namespace */

#endif /* __CVC4__DECISION__DECISION_ATTRIBUTES_H */

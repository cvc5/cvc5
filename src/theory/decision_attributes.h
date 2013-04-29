/*********************                                                        */
/*! \file decision_attributes.h
 ** \verbatim
 ** Original author: Kshitij Bansal
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Rewriter attributes
 **
 ** Rewriter attributes.
 **/

#ifndef __CVC4__THEORY__DECISION_ATRRIBUTES
#define __CVC4__THEORY__DECISION_ATRRIBUTES

#include "expr/attribute.h"

namespace CVC4 {
namespace decision {
typedef uint64_t DecisionWeight;
}
namespace theory {
namespace attr {
  struct DecisionWeightTag {};
}/* CVC4::theory::attr namespace */

typedef expr::Attribute<attr::DecisionWeightTag, decision::DecisionWeight> DecisionWeightAttr;

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DECISION_ATRRIBUTES */

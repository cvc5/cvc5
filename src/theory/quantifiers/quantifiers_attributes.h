/*********************                                                        */
/*! \file quantifiers_attributes.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Attributes for the theory quantifiers
 **
 ** Attributes for the theory quantifiers.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H
#define __CVC4__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H

#include "theory/rewriter.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

/** Attribute priority for rewrite rules */
//struct RrPriorityAttributeId {};
//typedef expr::Attribute< RrPriorityAttributeId, uint64_t > RrPriorityAttribute;

struct QuantifiersAttributes
{
  /** set user attribute
    *   This function will apply a custom set of attributes to all top-level universal
    *   quantifiers contained in n
    */
  static void setUserAttribute( const std::string& attr, Node n, std::vector< Node >& node_values, std::string str_value );
};


}
}
}

#endif

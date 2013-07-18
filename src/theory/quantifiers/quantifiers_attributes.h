/*********************                                                        */
/*! \file quantifiers_attributes.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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

/** Attribute true for quantifiers that are axioms */
struct AxiomAttributeId {};
typedef expr::Attribute< AxiomAttributeId, bool > AxiomAttribute;

/** Attribute true for quantifiers that are conjecture */
struct ConjectureAttributeId {};
typedef expr::Attribute< ConjectureAttributeId, bool > ConjectureAttribute;

/** Attribute priority for rewrite rules */
//struct RrPriorityAttributeId {};
//typedef expr::Attribute< RrPriorityAttributeId, uint64_t > RrPriorityAttribute;

struct QuantifiersAttributes
{
  /** set user attribute
    *   This function will apply a custom set of attributes to all top-level universal
    *   quantifiers contained in n
    */
  static void setUserAttribute( const std::string& attr, Node n );
};


}
}
}

#endif

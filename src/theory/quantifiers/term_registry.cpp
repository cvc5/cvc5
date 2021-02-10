/*********************                                                        */
/*! \file term_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term registry class
 **/

#include "theory/quantifiers/term_registry.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

TermRegistry::TermRegistry(QuantifiersState& qs,
                           QuantifiersInferenceManager& qim,
                           QuantifiersEngine* qe)
{
}

void TermRegistry::addTerm(Node n, bool withinQuant) {}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4

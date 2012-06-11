/*********************                                                        */
/*! \file instantiator_tables_template.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011, 2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Instantiator tables for quantifier-friendly theories
 **
 ** This file contains template code for the instantiator tables that are
 ** generated from the Theory kinds files.
 **/

#include "context/context.h"
#include "theory/quantifiers_engine.h"

${instantiator_includes}

#line 26 "${template}"

namespace CVC4 {
namespace theory {

Instantiator* Theory::makeInstantiator(context::Context* c, theory::QuantifiersEngine* qe) {
  switch(d_id) {
${make_instantiator_cases}
#line 34 "${template}"
  default:
    Unhandled(d_id);
  }
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

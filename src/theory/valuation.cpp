/*********************                                                        */
/*! \file valuation.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A "valuation" proxy for TheoryEngine
 **
 ** Implementation of Valuation class.
 **/

#include "expr/node.h"
#include "theory/valuation.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

Node Valuation::getValue(TNode n) {
  return d_engine->getValue(n);
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */

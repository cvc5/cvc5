/*********************                                                        */
/** decision_engine.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "util/decision_engine.h"
#include "util/Assert.h"
#include "expr/node.h"

namespace CVC4 {

DecisionEngine::~DecisionEngine() {
}

/**
 * Only here to permit compilation and linkage.  This may be pure
 * virtual in the final design (?)
 */
Node DecisionEngine::nextDecision() {
  Unimplemented();
}

}/* CVC4 namespace */

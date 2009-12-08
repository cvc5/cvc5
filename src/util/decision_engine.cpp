/*********************                                           -*- C++ -*-  */
/** decision_engine.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "util/decision_engine.h"
#include "util/Assert.h"
#include "util/literal.h"

namespace CVC4 {

DecisionEngine::~DecisionEngine() {
}

/**
 * Only here to permit compilation and linkage.  This may be pure
 * virtual in the final design (?)
 */
Literal DecisionEngine::nextDecision() {
  Unreachable();
}

}/* CVC4 namespace */

/*********************                                                        */
/*! \file logic_request.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/



#include "smt/logic_request.h"
#include "smt/smt_engine.h"


namespace CVC4 {

/** Widen the logic to include the given theory. */
void LogicRequest::widenLogic(theory::TheoryId id) {
  d_smt.d_logic.getUnlockedCopy();
  d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
  d_smt.d_logic.enableTheory(id);
  d_smt.d_logic.lock();
}

}/* CVC4 namespace */

/*********************                                                        */
/*! \file logic_request.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Martin Brain, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

/** Enable Integers if not yet enabled. */
void LogicRequest::enableIntegers()
{
  if (!d_smt.d_logic.areIntegersUsed())
  {
    d_smt.d_logic = d_smt.d_logic.getUnlockedCopy();
    d_smt.d_logic.enableIntegers();
    d_smt.d_logic.lock();
  }
}

}/* CVC4 namespace */

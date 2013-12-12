/*********************                                                        */
/*! \file smt_engine_check_proof.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "smt/smt_engine.h"
#include "check.h"

using namespace CVC4;
using namespace std;

void SmtEngine::checkProof() {

#ifdef CVC4_PROOF

  //TimerStat::CodeTimer checkProofTimer(d_stats->d_checkProofTime);

#else /* CVC4_PROOF */

  Unreachable("This version of CVC4 was built without proof support; cannot check proofs.");

#endif /* CVC4_PROOF */

}

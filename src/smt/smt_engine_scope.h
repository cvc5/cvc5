/*********************                                                        */
/*! \file smt_engine_scope.h
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

#include "cvc4_private.h"

#include "smt/smt_engine.h"
#include "util/tls.h"
#include "util/cvc4_assert.h"
#include "expr/node_manager.h"
#include "util/output.h"
#include "proof/proof.h"

#pragma once

namespace CVC4 {

class ProofManager;

namespace smt {

extern CVC4_THREADLOCAL(SmtEngine*) s_smtEngine_current;

inline SmtEngine* currentSmtEngine() {
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current;
}

inline ProofManager* currentProofManager() {
  Assert(PROOF_ON());
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current->d_proofManager;
}

class SmtScope : public NodeManagerScope {
  /** The old NodeManager, to be restored on destruction. */
  SmtEngine* d_oldSmtEngine;

public:

  SmtScope(const SmtEngine* smt) :
    NodeManagerScope(smt->d_nodeManager),
    d_oldSmtEngine(s_smtEngine_current) {
    Assert(smt != NULL);
    s_smtEngine_current = const_cast<SmtEngine*>(smt);
    Debug("current") << "smt scope: " << s_smtEngine_current << std::endl;
  }

  ~SmtScope() {
    s_smtEngine_current = d_oldSmtEngine;
    Debug("current") << "smt scope: returning to " << s_smtEngine_current << std::endl;
  }
};/* class SmtScope */

}/* CVC4::smt namespace */
}/* CVC4 namespace */

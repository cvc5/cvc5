#include "smt/smt_engine.h"
#include "util/tls.h"
#include "util/Assert.h"
#include "expr/node_manager.h"
#include "util/output.h"

#pragma once

namespace CVC4 {
namespace smt {

extern CVC4_THREADLOCAL(SmtEngine*) s_smtEngine_current;

inline SmtEngine* currentSmtEngine() {
  Assert(s_smtEngine_current != NULL);
  return s_smtEngine_current;
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

}
}

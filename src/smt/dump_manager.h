/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The dump manager of the SmtEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__DUMP_MANAGER_H
#define CVC5__SMT__DUMP_MANAGER_H

#include <memory>
#include <vector>

#include "expr/node.h"

namespace cvc5 {

class NodeCommand;

namespace context {
class UserContext;
}

namespace smt {

/**
 * This utility is responsible for:
 * implementing some dumping traces e.g. --dump=declarations.
 */
class DumpManager
{

 public:
  DumpManager(context::UserContext* u);
  ~DumpManager();
  /**
   * Finish init, called during SmtEngine::finishInit, which is triggered
   * when initialization of options is finished.
   */
  void finishInit();
  /**
   * Reset assertions, called on SmtEngine::resetAssertions.
   */
  void resetAssertions();
  /**
   * Add to dump command.  This is used for recording a command
   * that should be reported via the dumpTag trace.
   */
  void addToDump(const NodeCommand& c, const char* dumpTag = "declarations");

  /**
   * Set that function f should print in the model if and only if p is true.
   */
  void setPrintFuncInModel(Node f, bool p);

 private:
  /** Fully inited */
  bool d_fullyInited;
  /**
   * A vector of declaration commands waiting to be dumped out.
   * Once the SmtEngine is fully initialized, we'll dump them.
   * This ensures the declarations come after the set-logic and
   * any necessary set-option commands are dumped.
   */
  std::vector<std::unique_ptr<NodeCommand>> d_dumpCommands;
};

}  // namespace smt
}  // namespace cvc5

#endif

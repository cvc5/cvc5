/*********************                                                        */
/*! \file dump_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The dump manager of the SmtEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__DUMP_MANAGER_H
#define CVC4__SMT__DUMP_MANAGER_H

#include <memory>
#include <vector>

#include "context/cdlist.h"
#include "expr/node.h"

namespace CVC4 {

class NodeCommand;

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
   * Add to Model command.  This is used for recording a command
   * that should be reported during a get-model call.
   */
  void addToModelCommandAndDump(const NodeCommand& c,
                                uint32_t flags = 0,
                                bool userVisible = true,
                                const char* dumpTag = "declarations");

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
}  // namespace CVC4

#endif

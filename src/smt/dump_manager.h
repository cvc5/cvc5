/*********************                                                        */
/*! \file dump_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Abdalrhman Mohamed
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
 * (1) storing information required for SMT-LIB queries such as get-model,
 * which requires knowing what symbols are declared and should be printed in
 * the model.
 * (2) implementing some dumping traces e.g. --dump=declarations.
 */
class DumpManager
{
  typedef context::CDList<NodeCommand*> CommandList;

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
  /** get number of commands to report in a model */
  size_t getNumModelCommands() const;
  /** get model command at index i */
  const NodeCommand* getModelCommand(size_t i) const;

 private:
  /** Fully inited */
  bool d_fullyInited;

  /**
   * A list of commands that should be in the Model globally (i.e.,
   * regardless of push/pop).  Only maintained if produce-models option
   * is on.
   */
  std::vector<std::unique_ptr<NodeCommand>> d_modelGlobalCommands;

  /**
   * A list of commands that should be in the Model locally (i.e.,
   * it is context-dependent on push/pop).  Only maintained if
   * produce-models option is on.
   */
  CommandList d_modelCommands;
  /**
   * A list of model commands allocated to d_modelCommands at any time. This
   * is maintained for memory management purposes.
   */
  std::vector<std::unique_ptr<NodeCommand>> d_modelCommandsAlloc;

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

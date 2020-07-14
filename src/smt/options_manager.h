/*********************                                                        */
/*! \file options_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Module for managing options of an SmtEngine.
 **/

#ifndef CVC4__SMT__OPTIONS_MANAGER_H
#define CVC4__SMT__OPTIONS_MANAGER_H

#include "options/options.h"
#include "options/options_listener.h"

namespace CVC4 {

class SmtEngine;
class LogicInfo;
class ResourceManager;

namespace smt {

/**
 * This class is intended to be used by SmtEngine, and is responsible for:
 * (1) Implementing core options including timeouts and output preferences,
 * (2) Setting default values for options based on a logic.
 *
 * Notice that the constructor of this class retroactively sets all
 * necessary options that have already been set in the options object it is
 * given. This is to ensure that the command line arguments, which modified
 * on an options object in the driver, immediately take effect upon creation of
 * this class.
 */
class OptionsManager : public OptionsListener
{
 public:
  OptionsManager(Options* opts, ResourceManager* rm = nullptr);
  ~OptionsManager();
  /**
   * Called when a set option call is made on the options object associated
   * with this class. This handles all options that should be taken into account
   * immediately instead of e.g. at SmtEngine::finishInit time. This primarily
   * includes options related to parsing and output.
   *
   * This function call is made after the option has been updated. This means
   * that the value of the option can be queried in the options object that
   * this class is listening to.
   */
  void notifySetOption(const std::string& key) override;
  /**
   * Finish init, which is called at the beginning of SmtEngine::finishInit,
   * just before solving begins. This initializes the options pertaining to
   * time limits, and sets the default options.
   */
  void finishInit(LogicInfo& logic, bool isInternalSubsolver);

 private:
  /** Reference to the options object */
  Options* d_options;
  /** Pointer to the resource manager */
  ResourceManager* d_resourceManager;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__OPTIONS_MANAGER_H */

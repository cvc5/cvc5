/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__SMT_ENGINE_SCOPE_H
#define CVC5__SMT__SMT_ENGINE_SCOPE_H

#include "expr/node_manager.h"

#include "options/options.h"

namespace cvc5 {

class SmtEngine;
class StatisticsRegistry;

namespace smt {

SmtEngine* currentSmtEngine();
bool smtEngineInScope();

/** get the current resource manager */
ResourceManager* currentResourceManager();

class SmtScope : public NodeManagerScope
{
 public:
  SmtScope(const SmtEngine* smt);
  ~SmtScope();
  /**
   * This returns the StatisticsRegistry attached to the currently in scope
   * SmtEngine.
   */
  static StatisticsRegistry& currentStatisticsRegistry();

 private:
  /** The old SmtEngine, to be restored on destruction. */
  SmtEngine* d_oldSmtEngine;
  /** Options scope */
  Options::OptionsScope d_optionsScope;
};/* class SmtScope */

}  // namespace smt
}  // namespace cvc5

#endif /* CVC5__SMT__SMT_ENGINE_SCOPE_H */

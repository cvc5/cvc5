/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Module for managing options of an SmtEngine.
 */

#include "smt/options_manager.h"

#include "base/output.h"
#include "expr/expr_iomanip.h"
#include "options/base_options.h"
#include "options/expr_options.h"
#include "options/smt_options.h"
#include "smt/command.h"
#include "smt/dump.h"
#include "smt/set_defaults.h"
#include "util/resource_manager.h"

namespace cvc5 {
namespace smt {

OptionsManager::OptionsManager(Options* opts) : d_options(opts)
{
}

OptionsManager::~OptionsManager() {}

void OptionsManager::notifySetOption(const std::string& key)
{
}

void OptionsManager::finishInit(LogicInfo& logic, bool isInternalSubsolver)
{
  // ensure that our heuristics are properly set up
  setDefaults(logic, isInternalSubsolver);
}

}  // namespace smt
}  // namespace cvc5

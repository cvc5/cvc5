/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Header for main cvc5 driver.
 */

#include <cvc5/cvc5.h>

#include <memory>
#include <string>

#include "base/cvc5config.h"

#ifndef CVC5__MAIN__MAIN_H
#define CVC5__MAIN__MAIN_H

namespace cvc5::main {

class CommandExecutor;

/** Full argv[0] */
extern const char* progPath;

/** Just the basename component of argv[0] */
extern std::string progName;

/** A reference for use by the signal handlers to print statistics */
extern std::unique_ptr<CommandExecutor> pExecutor;

/**
 * If true, will not spin on segfault even when CVC5_DEBUG is on.
 * Useful for nightly regressions, noninteractive performance runs
 * etc.  See util.cpp.
 */
extern bool segvSpin;

}  // namespace cvc5::main

/** Actual cvc5 driver functions **/
int runCvc5(int argc, char* argv[], std::unique_ptr<cvc5::Solver>&);

#endif /* CVC5__MAIN__MAIN_H */

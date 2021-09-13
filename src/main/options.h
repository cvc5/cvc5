/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Options utilities used in the driver.
 */

#ifndef CVC5__MAIN__OPTIONS_H
#define CVC5__MAIN__OPTIONS_H

#include <iosfwd>
#include <string>
#include <vector>

#include "api/cpp/cvc5.h"

namespace cvc5::main {

/**
 * Print overall command-line option usage message, prefixed by
 * "msg"---which could be an error message causing the usage
 * output in the first place, e.g. "no such option --foo"
 */
void printUsage(const std::string& msg, std::ostream& os);

/**
 * Print command-line option usage message for only the most-commonly
 * used options.  The message is prefixed by "msg"---which could be
 * an error message causing the usage output in the first place, e.g.
 * "no such option --foo"
 */
void printShortUsage(const std::string& msg, std::ostream& os);

/** Print help for the --lang command line option */
void printLanguageHelp(std::ostream& os);

/**
 * Initialize the Options object options based on the given
 * command-line arguments given in argc and argv.  The return value
 * is what's left of the command line (that is, the non-option
 * arguments).
 *
 * This function uses getopt_long() and is not thread safe.
 *
 * Throws OptionException on failures.
 *
 * Preconditions: options and argv must be non-null.
 */
std::vector<std::string> parse(api::Solver& solver,
                               int argc,
                               char* argv[],
                               std::string& binaryName);

}  // namespace cvc5::options

#endif

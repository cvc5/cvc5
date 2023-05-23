/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Paul Meng, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Options utilities used in the driver.
 */

#ifndef CVC5__MAIN__OPTIONS_H
#define CVC5__MAIN__OPTIONS_H

#include <cvc5/cvc5.h>

#include <iosfwd>
#include <string>
#include <vector>

namespace cvc5::main {

/**
 * Print overall command-line option usage message to the given output stream
 * with binary being the command to run cvc5.
 */
void printUsage(const std::string& binary, std::ostream& os);

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
std::vector<std::string> parse(cvc5::Solver& solver,
                               int argc,
                               char* argv[],
                               std::string& binaryName);

}  // namespace cvc5::main

#endif

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
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_PUBLIC_H
#define CVC5__OPTIONS__OPTIONS_PUBLIC_H

#include <iosfwd>
#include <string>
#include <vector>

#include "cvc5_export.h"
#include "options/options.h"

namespace cvc5::options {

bool getUfHo(const Options& opts) CVC5_EXPORT;

/**
 * Get a description of the command-line flags accepted by
 * parse.  The returned string will be escaped so that it is
 * suitable as an argument to printf. */
const std::string& getDescription() CVC5_EXPORT;

/**
 * Print overall command-line option usage message, prefixed by
 * "msg"---which could be an error message causing the usage
 * output in the first place, e.g. "no such option --foo"
 */
void printUsage(const std::string& msg, std::ostream& os) CVC5_EXPORT;

/**
 * Print command-line option usage message for only the most-commonly
 * used options.  The message is prefixed by "msg"---which could be
 * an error message causing the usage output in the first place, e.g.
 * "no such option --foo"
 */
void printShortUsage(const std::string& msg, std::ostream& os) CVC5_EXPORT;

/** Print help for the --lang command line option */
void printLanguageHelp(std::ostream& os) CVC5_EXPORT;

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
std::vector<std::string> parse(Options& opts,
                               int argc,
                               char* argv[],
                               std::string& binaryName) CVC5_EXPORT;

/**
 * Retrieve an option value by name (as given in key) from the Options object
 * opts as a string.
 */
std::string get(const Options& opts, const std::string& name) CVC5_EXPORT;

/**
 * Update the Options object opts, set the value of the option specified by key
 * to the value parsed from optionarg.
 */
void set(Options& opts,
         const std::string& name,
         const std::string& optionarg) CVC5_EXPORT;

/**
 * Get the setting for all options.
 */
std::vector<std::vector<std::string> > getAll(const Options& opts) CVC5_EXPORT;

/**
 * Get a (sorted) list of all option names that are available.
 */
std::vector<std::string> getNames() CVC5_EXPORT;

}  // namespace cvc5::options

#endif

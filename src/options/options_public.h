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

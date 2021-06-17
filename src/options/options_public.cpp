/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Gereon Kremer, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Definitions of public facing interface functions for Options.
 *
 * These are all one line wrappers for accessing the internal option data.
 */

#include "options_public.h"

#include "options/uf_options.h"

namespace cvc5::options {

bool getUfHo(const Options& opts) { return opts.uf.ufHo; }

}  // namespace cvc5::options

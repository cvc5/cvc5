/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains code for handling command-line options.
 */

#include "options/options.h"

#include "base/check.h"
#include "base/cvc5config.h"
#include "options/options_handler.h"
#include "options/options_listener.h"

// clang-format off
${headers_module}$
// clang-format on

namespace cvc5::internal
{
  Options::Options()
      :
// clang-format off
${holder_mem_inits}$
${holder_ref_inits}$
// clang-format on
        d_handler(std::make_unique<options::OptionsHandler>(this))
  {
  }

  Options::~Options() {}

// clang-format off
${write_functions}$
// clang-format on

  void Options::copyValues(const Options& options)
  {
    if (this != &options)
    {
// clang-format off
${holder_mem_copy}$
// clang-format on
    }
  }

}  // namespace cvc5::internal


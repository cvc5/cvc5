/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Contains code for handling command-line options.
 */

#include "options/options.h"

#include "base/check.h"
#include "base/exception.h"
#include "base/output.h"
#include "options/language.h"
#include "options/options_handler.h"
#include "options/options_listener.h"

// clang-format off
${headers_module}$

#include "base/cvc5config.h"

${headers_handler}$

using namespace cvc5;
using namespace cvc5::options;
// clang-format on

namespace cvc5
{
  thread_local Options* Options::s_current = nullptr;

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

void Options::copyValues(const Options& options){
  if(this != &options) {
// clang-format off
${holder_mem_copy}$
// clang-format on
  }
}

}  // namespace cvc5


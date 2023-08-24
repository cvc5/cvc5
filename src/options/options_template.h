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
 * Global (command-line, set-option, ...) parameters for SMT.
 */

#include "cvc5_public.h"

#ifndef CVC5__OPTIONS__OPTIONS_H
#define CVC5__OPTIONS__OPTIONS_H

#include <cvc5/cvc5_export.h>

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

namespace cvc5::internal {
namespace options {
  class OptionsHandler;
// clang-format off
${holder_fwd_decls}$
// clang-format on
}  // namespace options

class OptionsListener;

class CVC5_EXPORT Options
{
  public:
  /**
   * Options cannot be copied as they are given an explicit list of
   * Listeners to respond to.
   */
  Options(const Options& options) = delete;

  /**
   * Options cannot be assigned as they are given an explicit list of
   * Listeners to respond to.
   */
  Options& operator=(const Options& options) = delete;

  Options();
  ~Options();

  options::OptionsHandler& handler() const {
    return *d_handler;
  }

  /**
   * Copies the value of the options stored in OptionsHolder into the current
   * Options object.
   */
  void copyValues(const Options& options);

 private:

// clang-format off
${holder_mem_decls}$
// clang-format on
 public:
// clang-format off
${holder_ref_decls}$
// clang-format on
  
 private:
  /** The handler for the options of the theory. */
  std::unique_ptr<options::OptionsHandler> d_handler;
}; /* class Options */

}  // namespace cvc5::internal

#endif /* CVC5__OPTIONS__OPTIONS_H */

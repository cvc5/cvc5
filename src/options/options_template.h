/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Paul Meng
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

#ifndef CVC5__OPTIONS__OPTIONS_H
#define CVC5__OPTIONS__OPTIONS_H

#include <iosfwd>
#include <memory>
#include <string>
#include <vector>

#include "cvc5_export.h"

namespace cvc5 {
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

  class OptionsScope
  {
   private:
     Options* d_oldOptions;
   public:
     OptionsScope(Options* newOptions) :
         d_oldOptions(Options::s_current)
     {
       Options::s_current = newOptions;
     }
     ~OptionsScope(){
       Options::s_current = d_oldOptions;
     }
  };
  friend class OptionsScope;

  /** Return true if current Options are null */
  static inline bool isCurrentNull() {
    return s_current == nullptr;
  }

  /** Get the current Options in effect */
  static inline Options& current() {
    return *s_current;
  }

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

  /** The current Options in effect */
  static thread_local Options* s_current;


}; /* class Options */

}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTIONS_H */

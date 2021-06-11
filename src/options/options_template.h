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

#include "base/listener.h"
#include "cvc5_export.h"
#include "options/language.h"
#include "options/printer_modes.h"

namespace cvc5 {

namespace api {
class Solver;
}
namespace options {
  struct OptionsHolder;
  class OptionsHandler;
// clang-format off
${holder_fwd_decls}$
// clang-format on
  }  // namespace options

class OptionsListener;

class CVC5_EXPORT Options
{
  friend api::Solver;

  /** The handler for the options of the theory. */
  options::OptionsHandler* d_handler;

// clang-format off
${holder_mem_decls}$
// clang-format on
 public:
// clang-format off
${holder_ref_decls}$
// clang-format on
  
 private:

  /** The current Options in effect */
  static thread_local Options* s_current;

  friend class options::OptionsHandler;

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

public:
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

  /** Return true if current Options are null */
  static inline bool isCurrentNull() {
    return s_current == NULL;
  }

  /** Get the current Options in effect */
  static inline Options& current() {
    return *s_current;
  }

  Options(OptionsListener* ol = nullptr);
  ~Options();

  options::OptionsHandler& handler() const {
    return *d_handler;
  }

  /**
   * Copies the value of the options stored in OptionsHolder into the current
   * Options object.
   * This does not copy the listeners in the Options object.
   */
  void copyValues(const Options& options);

  /**
   * Set the value of the given option by key.
   *
   * Throws OptionException or ModalException on failures.
   */
  void setOption(const std::string& key, const std::string& optionarg);

  /**
   * Gets the value of the given option by key and returns value as a string.
   *
   * Throws OptionException on failures, such as key not being the name of an
   * option.
   */
  std::string getOption(const std::string& key) const;

  // Static accessor functions.
  // TODO: Document these.
  static std::ostream* currentGetOut();

  /**
   * Get a description of the command-line flags accepted by
   * parseOptions.  The returned string will be escaped so that it is
   * suitable as an argument to printf. */
  std::string getDescription() const;

  /**
   * Print overall command-line option usage message, prefixed by
   * "msg"---which could be an error message causing the usage
   * output in the first place, e.g. "no such option --foo"
   */
  static void printUsage(const std::string msg, std::ostream& out);

  /**
   * Print command-line option usage message for only the most-commonly
   * used options.  The message is prefixed by "msg"---which could be
   * an error message causing the usage output in the first place, e.g.
   * "no such option --foo"
   */
  static void printShortUsage(const std::string msg, std::ostream& out);

  /** Print help for the --lang command line option */
  static void printLanguageHelp(std::ostream& out);

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
  static std::vector<std::string> parseOptions(Options* options,
                                               int argc,
                                               char* argv[],
                                               std::string& binaryName);

  /**
   * Get the setting for all options.
   */
  std::vector<std::vector<std::string> > getOptions() const;

  /** Set the generic listener associated with this class to ol */
  void setListener(OptionsListener* ol);

  /** Sends a std::flush to getErr(). */
  void flushErr();

  /** Sends a std::flush to getOut(). */
  void flushOut();

 private:
  /** Pointer to the options listener, if one exists */
  OptionsListener* d_olisten;
  /**
   * Helper method for setOption, updates this object for setting the given
   * option.
   */
  void setOptionInternal(const std::string& key, const std::string& optionarg);
  /**
   * Internal procedure for implementing the parseOptions function.
   * Initializes the options object based on the given command-line
   * arguments. The command line arguments are stored in argc/argv.
   * Nonoptions are stored into nonoptions.
   *
   * This is not thread safe.
   *
   * Throws OptionException on failures.
   *
   * Preconditions: options, extender and nonoptions are non-null.
   */
  void parseOptionsRecursive(int argc,
                                    char* argv[],
                                    std::vector<std::string>* nonoptions);
}; /* class Options */

}  // namespace cvc5

#endif /* CVC5__OPTIONS__OPTIONS_H */

/*********************                                                        */
/*! \file options.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT.
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__OPTIONS__OPTIONS_H
#define __CVC4__OPTIONS__OPTIONS_H

#include <iostream>
#include <fstream>
#include <string>
#include <vector>

#include "options/option_exception.h"
#include "util/language.h"
#include "util/tls.h"

namespace CVC4 {

namespace options {
  struct OptionsHolder;
}/* CVC4::options namespace */

class ExprStream;
class NodeManager;
class NodeManagerScope;
class SmtEngine;

class CVC4_PUBLIC Options {
  /** The struct that holds all option values. */
  options::OptionsHolder* d_holder;

  /** The current Options in effect */
  static CVC4_THREADLOCAL(Options*) s_current;

  /** Low-level assignment function for options */
  template <class T>
  void assign(T, std::string option, std::string value, SmtEngine* smt);
  /** Low-level assignment function for bool-valued options */
  template <class T>
  void assignBool(T, std::string option, bool value, SmtEngine* smt);

  friend class NodeManager;
  friend class NodeManagerScope;
  friend class SmtEngine;

public:

  /** Get the current Options in effect */
  static inline Options& current() {
    return *s_current;
  }

  Options();
  Options(const Options& options);
  ~Options();

  /**
   * Set the value of the given option.  Use of this default
   * implementation causes a compile-time error; write-able
   * options specialize this template with a real implementation.
   */
  template <class T>
  void set(T, const typename T::type&) {
    // Flag a compile-time error.  Write-able options specialize
    // this template to provide an implementation.
    T::you_are_trying_to_assign_to_a_read_only_option;
  }

  /** Get the value of the given option.  Const access only. */
  template <class T>
  const typename T::type& operator[](T) const;

  /**
   * Returns true iff the value of the given option was set
   * by the user via a command-line option or SmtEngine::setOption().
   * (Options::set() is low-level and doesn't count.)  Returns false
   * otherwise.
   */
  template <class T>
  bool wasSetByUser(T) const;

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
   * Initialize the options based on the given command-line arguments.
   * The return value is what's left of the command line (that is, the
   * non-option arguments).
   */
  std::vector<std::string> parseOptions(int argc, char* argv[]) throw(OptionException);

};/* class Options */

}/* CVC4 namespace */

#include "options/base_options.h"

#endif /* __CVC4__OPTIONS__OPTIONS_H */

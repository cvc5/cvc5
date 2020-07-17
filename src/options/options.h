/*********************                                                        */
/*! \file options.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Global (command-line, set-option, ...) parameters for SMT.
 **
 ** Global (command-line, set-option, ...) parameters for SMT.
 **/

#include "cvc4_public.h"

#ifndef CVC4__OPTIONS__OPTIONS_H
#define CVC4__OPTIONS__OPTIONS_H

#include <fstream>
#include <ostream>
#include <string>
#include <vector>

#include "base/listener.h"
#include "base/modal_exception.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/printer_modes.h"

namespace CVC4 {

namespace api {
class Solver;
}
namespace options {
  struct OptionsHolder;
  class OptionsHandler;
}/* CVC4::options namespace */

class OptionsListener;

class CVC4_PUBLIC Options {
  friend api::Solver;
  /** The struct that holds all option values. */
  options::OptionsHolder* d_holder;

  /** The handler for the options of the theory. */
  options::OptionsHandler* d_handler;

  /** The current Options in effect */
  static thread_local Options* s_current;

  /** Low-level assignment function for options */
  template <class T>
  void assign(T, std::string option, std::string value);
  /** Low-level assignment function for bool-valued options */
  template <class T>
  void assignBool(T, std::string option, bool value);

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

  static std::string formatThreadOptionException(const std::string& option);

  static const size_t s_maxoptlen = 128;
  static const unsigned s_preemptAdditional = 6;

public:
  class CVC4_PUBLIC OptionsScope {
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
  static inline Options* current() {
    return s_current;
  }

  Options(OptionsListener* ol = nullptr);
  ~Options();

  /**
   * Copies the value of the options stored in OptionsHolder into the current
   * Options object.
   * This does not copy the listeners in the Options object.
   */
  void copyValues(const Options& options);

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

  /**
   * Set the value of the given option by key.
   *
   * Throws OptionException or ModalException on failures.
   */
  void setOption(const std::string& key, const std::string& optionarg);

  /** Get the value of the given option.  Const access only. */
  template <class T>
  const typename T::type& operator[](T) const;

  /**
   * Gets the value of the given option by key and returns value as a string.
   *
   * Throws OptionException on failures, such as key not being the name of an
   * option.
   */
  std::string getOption(const std::string& key) const;

  // Get accessor functions.
  InputLanguage getInputLanguage() const;
  options::InstFormatMode getInstFormatMode() const;
  OutputLanguage getOutputLanguage() const;
  bool getUfHo() const;
  bool getCheckProofs() const;
  bool getDumpInstantiations() const;
  bool getDumpModels() const;
  bool getDumpProofs() const;
  bool getDumpSynth() const;
  bool getDumpUnsatCores() const;
  bool getEarlyExit() const;
  bool getFilesystemAccess() const;
  bool getForceNoLimitCpuWhileDump() const;
  bool getHelp() const;
  bool getIncrementalSolving() const;
  bool getInteractive() const;
  bool getInteractivePrompt() const;
  bool getLanguageHelp() const;
  bool getMemoryMap() const;
  bool getParseOnly() const;
  bool getProduceModels() const;
  bool getProof() const;
  bool getSegvSpin() const;
  bool getSemanticChecks() const;
  bool getStatistics() const;
  bool getStatsEveryQuery() const;
  bool getStatsHideZeros() const;
  bool getStrictParsing() const;
  int getTearDownIncremental() const;
  unsigned long getCumulativeTimeLimit() const;
  bool getVersion() const;
  const std::string& getForceLogicString() const;
  int getVerbosity() const;
  std::istream* getIn() const;
  std::ostream* getErr();
  std::ostream* getOut();
  std::ostream* getOutConst() const; // TODO: Remove this.
  std::string getBinaryName() const;
  unsigned getParseStep() const;

  // TODO: Document these.
  void setInputLanguage(InputLanguage);
  void setInteractive(bool);
  void setOut(std::ostream*);
  void setOutputLanguage(OutputLanguage);

  bool wasSetByUserDumpSynth() const;
  bool wasSetByUserEarlyExit() const;
  bool wasSetByUserForceLogicString() const;
  bool wasSetByUserIncrementalSolving() const;
  bool wasSetByUserInteractive() const;

  // Static accessor functions.
  // TODO: Document these.
  static std::ostream* currentGetOut();

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
   * Look up long command-line option names that bear some similarity
   * to the given name.  Returns an empty string if there are no
   * suggestions.
   */
  static std::string suggestCommandLineOptions(const std::string& optionName);

  /**
   * Look up SMT option names that bear some similarity to
   * the given name.  Don't include the initial ":".  This might be
   * useful in case of typos.  Can return an empty vector if there are
   * no suggestions.
   */
  static std::vector<std::string> suggestSmtOptions(
      const std::string& optionName);

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
                                               char* argv[]);

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
  static void parseOptionsRecursive(Options* options,
                                    int argc,
                                    char* argv[],
                                    std::vector<std::string>* nonoptions);
};/* class Options */

}/* CVC4 namespace */

#endif /* CVC4__OPTIONS__OPTIONS_H */

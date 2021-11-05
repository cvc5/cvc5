/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interface for custom handlers and predicates options.
 */

#include "cvc5_private.h"

#ifndef CVC5__OPTIONS__OPTIONS_HANDLER_H
#define CVC5__OPTIONS__OPTIONS_HANDLER_H

#include <ostream>
#include <sstream>
#include <string>

#include "options/bv_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/managed_streams.h"
#include "options/option_exception.h"
#include "options/quantifiers_options.h"

namespace cvc5 {

class Options;

namespace options {

/**
 * Class that responds to command line options being set.
 *
 * Most functions can throw an OptionException on failure.
 */
class OptionsHandler
{
 public:
  OptionsHandler(Options* options);

  template <typename T>
  void checkMinimum(const std::string& flag, T value, T minimum) const
  {
    if (value < minimum)
    {
      std::stringstream ss;
      ss << flag << " = " << value
         << " is not a legal setting, value should be at least " << minimum
         << ".";
      throw OptionException(ss.str());
    }
  }
  template <typename T>
  void checkMaximum(const std::string& flag, T value, T maximum) const
  {
    if (value > maximum)
    {
      std::stringstream ss;
      ss << flag << " = " << value
         << " is not a legal setting, value should be at most " << maximum
         << ".";
      throw OptionException(ss.str());
    }
  }

  /******************************* base options *******************************/
  /** Apply the error output stream to the different output channels */
  void setErrStream(const std::string& flag, const ManagedErr& me);

  /** Convert option value to Language enum */
  Language stringToLanguage(const std::string& flag, const std::string& optarg);
  /** Check that lang is not LANG_AST (not allowed as input language) */
  void languageIsNotAST(const std::string& flag, Language lang);
  /** Apply the output language to the default output stream */
  void applyOutputLanguage(const std::string& flag, Language lang);
  /** Apply verbosity to the different output channels */
  void setVerbosity(const std::string& flag, int value);
  /** Decrease verbosity and call setVerbosity */
  void decreaseVerbosity(const std::string& flag);
  /** Increase verbosity and call setVerbosity */
  void increaseVerbosity(const std::string& flag);
  /** If statistics are disabled, disable statistics sub-options */
  void setStats(const std::string& flag, bool value);
  /** If statistics sub-option is disabled, enable statistics */
  void setStatsDetail(const std::string& flag, bool value);
  /** Enable a particular trace tag */
  void enableTraceTag(const std::string& flag, const std::string& optarg);
  /** Enable a particular debug tag */
  void enableDebugTag(const std::string& flag, const std::string& optarg);
  /** Enable a particular output tag */
  void enableOutputTag(const std::string& flag, const std::string& optarg);
  /** Apply print success flag to the different output channels */
  void setPrintSuccess(const std::string& flag, bool value);
  /** Pass the resource weight specification to the resource manager */
  void setResourceWeight(const std::string& flag, const std::string& optarg);

  /******************************* bv options *******************************/

  /** Check that abc is enabled */
  void abcEnabledBuild(const std::string& flag, bool value);
  /** Check that abc is enabled */
  void abcEnabledBuild(const std::string& flag, const std::string& value);
  /** Check that the sat solver mode is compatible with other bv options */
  void checkBvSatSolver(const std::string& flag, SatSolverMode m);
  /** Check that we use eager bitblasting for aig */
  void setBitblastAig(const std::string& flag, bool arg);

  /******************************* expr options *******************************/
  /** Set ExprSetDepth on all output streams */
  void setDefaultExprDepth(const std::string& flag, int depth);
  /** Set ExprDag on all output streams */
  void setDefaultDagThresh(const std::string& flag, int dag);

  /******************************* main options *******************************/
  /** Show the solver build configuration and exit */
  void showConfiguration(const std::string& flag);
  /** Show copyright information and exit */
  void showCopyright(const std::string& flag);
  /** Show version information and exit */
  void showVersion(const std::string& flag);
  /** Show all debug tags and exit */
  void showDebugTags(const std::string& flag);
  /** Show all trace tags and exit */
  void showTraceTags(const std::string& flag);

 private:
  /** Pointer to the containing Options object.*/
  Options* d_options;
}; /* class OptionHandler */

}  // namespace options
}  // namespace cvc5

#endif /*  CVC5__OPTIONS__OPTIONS_HANDLER_H */

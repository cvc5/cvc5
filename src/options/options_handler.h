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
class OptionsHandler {
public:
  OptionsHandler(Options* options);

  template <typename T>
  void checkMinimum(const std::string& option,
                    const std::string& flag,
                    T value,
                    T minimum) const
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
  void checkMaximum(const std::string& option,
                    const std::string& flag,
                    T value,
                    T maximum) const
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

  // theory/quantifiers/options_handlers.h
  void checkInstWhenMode(const std::string& option,
                         const std::string& flag,
                         InstWhenMode mode);

  // theory/bv/options_handlers.h
  void abcEnabledBuild(const std::string& option,
                       const std::string& flag,
                       bool value);
  void abcEnabledBuild(const std::string& option,
                       const std::string& flag,
                       const std::string& value);

  void checkBvSatSolver(const std::string& option,
                        const std::string& flag,
                        SatSolverMode m);
  void checkBitblastMode(const std::string& option,
                         const std::string& flag,
                         BitblastMode m);

  void setBitblastAig(const std::string& option,
                      const std::string& flag,
                      bool arg);

  /**
   * Throws a ModalException if this option is being set after final
   * initialization.
   */
  void setProduceAssertions(const std::string& option,
                            const std::string& flag,
                            bool value);

  void setStats(const std::string& option, const std::string& flag, bool value);

  uint64_t limitHandler(const std::string& option,
                        const std::string& flag,
                        const std::string& optarg);
  void setResourceWeight(const std::string& option,
                         const std::string& flag,
                         const std::string& optarg);

  /* expr/options_handlers.h */
  void setDefaultExprDepth(const std::string& option,
                           const std::string& flag,
                           int depth);
  void setDefaultDagThresh(const std::string& option,
                           const std::string& flag,
                           int dag);

  /* main/options_handlers.h */
  void copyright(const std::string& option, const std::string& flag);
  void showConfiguration(const std::string& option, const std::string& flag);
  void showDebugTags(const std::string& option, const std::string& flag);
  void showTraceTags(const std::string& option, const std::string& flag);
  void threadN(const std::string& option, const std::string& flag);

  /* options/base_options_handlers.h */
  void setDumpStream(const std::string& option,
                     const std::string& flag,
                     const ManagedOut& mo);
  void setErrStream(const std::string& option,
                    const std::string& flag,
                    const ManagedErr& me);
  void setInStream(const std::string& option,
                   const std::string& flag,
                   const ManagedIn& mi);
  void setOutStream(const std::string& option,
                    const std::string& flag,
                    const ManagedOut& mo);
  void setVerbosity(const std::string& option,
                    const std::string& flag,
                    int value);
  void increaseVerbosity(const std::string& option, const std::string& flag);
  void decreaseVerbosity(const std::string& option, const std::string& flag);
  /** Convert optarg to Language enum */
  Language stringToLanguage(const std::string& option,
                            const std::string& flag,
                            const std::string& optarg);
  /** Apply the output language to the default output stream */
  void applyOutputLanguage(const std::string& option,
                           const std::string& flag,
                           Language lang);
  /** Check that lang is not LANG_AST (which is not allowed as input language). */
  void languageIsNotAST(const std::string& option,
                        const std::string& flag,
                        Language lang);
  void enableTraceTag(const std::string& option,
                      const std::string& flag,
                      const std::string& optarg);
  void enableDebugTag(const std::string& option,
                      const std::string& flag,
                      const std::string& optarg);

  void enableOutputTag(const std::string& option,
                       const std::string& flag,
                       const std::string& optarg);

  void setDumpMode(const std::string& option,
                   const std::string& flag,
                   const std::string& optarg);
  void setPrintSuccess(const std::string& option,
                       const std::string& flag,
                       bool value);

 private:

  /** Pointer to the containing Options object.*/
  Options* d_options;
}; /* class OptionHandler */

}  // namespace options
}  // namespace cvc5

#endif /*  CVC5__OPTIONS__OPTIONS_HANDLER_H */

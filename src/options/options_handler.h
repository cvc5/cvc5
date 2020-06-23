/*********************                                                        */
/*! \file options_handler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "cvc4_private.h"

#ifndef CVC4__OPTIONS__OPTIONS_HANDLER_H
#define CVC4__OPTIONS__OPTIONS_HANDLER_H

#include <ostream>
#include <string>

#include "base/modal_exception.h"
#include "options/base_handlers.h"
#include "options/bv_options.h"
#include "options/decision_options.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/printer_modes.h"
#include "options/quantifiers_options.h"

namespace CVC4 {
namespace options {

/**
 * Class that responds to command line options being set.
 *
 * Most functions can throw an OptionException on failure.
 */
class OptionsHandler {
public:
  OptionsHandler(Options* options);

  void unsignedGreater0(const std::string& option, unsigned value) {
    options::greater(0)(option, value);
  }

  void unsignedLessEqual2(const std::string& option, unsigned value) {
    options::less_equal(2)(option, value);
  }

  void doubleGreaterOrEqual0(const std::string& option, double value) {
    options::greater_equal(0.0)(option, value);
  }

  void doubleLessOrEqual1(const std::string& option, double value) {
    options::less_equal(1.0)(option, value);
  }

  // theory/quantifiers/options_handlers.h
  void checkInstWhenMode(std::string option, InstWhenMode mode);

  // theory/bv/options_handlers.h
  void abcEnabledBuild(std::string option, bool value);
  void abcEnabledBuild(std::string option, std::string value);

  template<class T> void checkSatSolverEnabled(std::string option, T m);

  void checkBvSatSolver(std::string option, SatSolverMode m);
  void checkBitblastMode(std::string option, BitblastMode m);

  void setBitblastAig(std::string option, bool arg);

  // printer/options_handlers.h
  InstFormatMode stringToInstFormatMode(std::string option, std::string optarg);

  // decision/options_handlers.h
  void setDecisionModeStopOnly(std::string option, DecisionMode m);

  /**
   * Throws a ModalException if this option is being set after final
   * initialization.
   */
  void notifyBeforeSearch(const std::string& option);
  void notifyDumpMode(std::string option);
  void setProduceAssertions(std::string option, bool value);
  void proofEnabledBuild(std::string option, bool value);
  void LFSCEnabledBuild(std::string option, bool value);
  void notifyDumpToFile(std::string option);
  void notifySetRegularOutputChannel(std::string option);
  void notifySetDiagnosticOutputChannel(std::string option);

  void statsEnabledBuild(std::string option, bool value);

  unsigned long limitHandler(std::string option, std::string optarg);

  void notifyTlimit(const std::string& option);
  void notifyTlimitPer(const std::string& option);
  void notifyRlimit(const std::string& option);
  void notifyRlimitPer(const std::string& option);


  /* expr/options_handlers.h */
  void setDefaultExprDepthPredicate(std::string option, int depth);
  void setDefaultDagThreshPredicate(std::string option, int dag);
  void notifySetDefaultExprDepth(std::string option);
  void notifySetDefaultDagThresh(std::string option);
  void notifySetPrintExprTypes(std::string option);

  /* main/options_handlers.h */
  void copyright(std::string option);
  void showConfiguration(std::string option);
  void showDebugTags(std::string option);
  void showTraceTags(std::string option);
  void threadN(std::string option);

  /* options/base_options_handlers.h */
  void setVerbosity(std::string option, int value);
  void increaseVerbosity(std::string option);
  void decreaseVerbosity(std::string option);
  OutputLanguage stringToOutputLanguage(std::string option, std::string optarg);
  InputLanguage stringToInputLanguage(std::string option, std::string optarg);
  void enableTraceTag(std::string option, std::string optarg);
  void enableDebugTag(std::string option, std::string optarg);
  void notifyPrintSuccess(std::string option);

 private:

  /** Pointer to the containing Options object.*/
  Options* d_options;

  /* Help strings */
  static const std::string s_instFormatHelp;

}; /* class OptionHandler */

template<class T>
void OptionsHandler::checkSatSolverEnabled(std::string option, T m)
{
#if !defined(CVC4_USE_CRYPTOMINISAT) && !defined(CVC4_USE_CADICAL) \
    && !defined(CVC4_USE_KISSAT)
  std::stringstream ss;
  ss << "option `" << option
     << "' requires CVC4 to be built with CryptoMiniSat or CaDiCaL or Kissat";
  throw OptionException(ss.str());
#endif
}

}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /*  CVC4__OPTIONS__OPTIONS_HANDLER_H */

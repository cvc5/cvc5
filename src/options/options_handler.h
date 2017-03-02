/*********************                                                        */
/*! \file options_handler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__OPTIONS__OPTIONS_HANDLER_H
#define __CVC4__OPTIONS__OPTIONS_HANDLER_H

#include <ostream>
#include <string>

#include "base/modal_exception.h"
#include "options/arith_heuristic_pivot_rule.h"
#include "options/arith_propagation_mode.h"
#include "options/arith_unate_lemma_mode.h"
#include "options/base_handlers.h"
#include "options/bv_bitblast_mode.h"
#include "options/decision_mode.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/simplification_mode.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

namespace CVC4 {
namespace options {

class OptionsHandler {
public:
  OptionsHandler(Options* options);
  virtual ~OptionsHandler() {}

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

  // DONE
  // decision/options_handlers.h
  // expr/options_handlers.h
  // main/options_handlers.h
  // options/base_options_handlers.h
  // printer/options_handlers.h
  // smt/options_handlers.h
  // theory/options_handlers.h
  // theory/booleans/options_handlers.h
  // theory/uf/options_handlers.h
  // theory/bv/options_handlers.h
  // theory/quantifiers/options_handlers.h
  // theory/arith/options_handlers.h


  // theory/arith/options_handlers.h
  ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option, std::string optarg) throw(OptionException);
  ArithPropagationMode stringToArithPropagationMode(std::string option, std::string optarg) throw(OptionException);
  ErrorSelectionRule stringToErrorSelectionRule(std::string option, std::string optarg) throw(OptionException);

  // theory/quantifiers/options_handlers.h
  theory::quantifiers::InstWhenMode stringToInstWhenMode(std::string option, std::string optarg) throw(OptionException);
  void checkInstWhenMode(std::string option, theory::quantifiers::InstWhenMode mode) throw(OptionException);
  theory::quantifiers::LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg) throw(OptionException);
  void checkLiteralMatchMode(std::string option, theory::quantifiers::LiteralMatchMode mode) throw(OptionException);
  theory::quantifiers::MbqiMode stringToMbqiMode(std::string option, std::string optarg) throw(OptionException);
  void checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode) throw(OptionException);
  theory::quantifiers::QcfWhenMode stringToQcfWhenMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::QcfMode stringToQcfMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::UserPatMode stringToUserPatMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::TriggerSelMode stringToTriggerSelMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::TriggerActiveSelMode stringToTriggerActiveSelMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::PrenexQuantMode stringToPrenexQuantMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::CegqiFairMode stringToCegqiFairMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::TermDbMode stringToTermDbMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::IteLiftQuantMode stringToIteLiftQuantMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::CegqiSingleInvMode stringToCegqiSingleInvMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::SygusInvTemplMode stringToSygusInvTemplMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::MacrosQuantMode stringToMacrosQuantMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::QuantDSplitMode stringToQuantDSplitMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::QuantRepMode stringToQuantRepMode(std::string option, std::string optarg) throw(OptionException);
  theory::quantifiers::FmfBoundMinMode stringToFmfBoundMinMode(std::string option, std::string optarg) throw(OptionException);

  // theory/bv/options_handlers.h
  void abcEnabledBuild(std::string option, bool value) throw(OptionException);
  void abcEnabledBuild(std::string option, std::string value) throw(OptionException);
  void satSolverEnabledBuild(std::string option, bool value) throw(OptionException);
  void satSolverEnabledBuild(std::string option, std::string optarg) throw(OptionException);

  theory::bv::BitblastMode stringToBitblastMode(std::string option, std::string optarg) throw(OptionException);
  theory::bv::BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg) throw(OptionException);
  void setBitblastAig(std::string option, bool arg) throw(OptionException);

  theory::bv::SatSolverMode stringToSatSolver(std::string option, std::string optarg) throw(OptionException);
    
  // theory/uf/options_handlers.h
  theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg) throw(OptionException);

  // theory/options_handlers.h
  theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg);
  void notifyUseTheoryList(std::string option);
  std::string handleUseTheoryList(std::string option, std::string optarg);


  // printer/options_handlers.h
  ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg) throw(OptionException);
  InstFormatMode stringToInstFormatMode(std::string option, std::string optarg) throw(OptionException);

  // decision/options_handlers.h
  decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg) throw(OptionException);
  decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg) throw(OptionException);


  /* smt/options_handlers.h */
  void notifyForceLogic(const std::string& option);
  void notifyBeforeSearch(const std::string& option) throw(ModalException);
  void notifyDumpMode(std::string option) throw(OptionException);
  SimplificationMode stringToSimplificationMode(std::string option, std::string optarg) throw(OptionException);
  void setProduceAssertions(std::string option, bool value) throw();
  void proofEnabledBuild(std::string option, bool value) throw(OptionException);
  void notifyDumpToFile(std::string option);
  void notifySetRegularOutputChannel(std::string option);
  void notifySetDiagnosticOutputChannel(std::string option);
  std::string checkReplayFilename(std::string option, std::string optarg);
  void notifySetReplayLogFilename(std::string option);

  void statsEnabledBuild(std::string option, bool value) throw(OptionException);

  unsigned long tlimitHandler(std::string option, std::string optarg) throw(OptionException);
  unsigned long tlimitPerHandler(std::string option, std::string optarg) throw(OptionException);
  unsigned long rlimitHandler(std::string option, std::string optarg) throw(OptionException);
  unsigned long rlimitPerHandler(std::string option, std::string optarg) throw(OptionException);

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
  void showConfiguration(std::string option);
  void showDebugTags(std::string option);
  void showTraceTags(std::string option);
  void threadN(std::string option);

  /* options/base_options_handlers.h */
  void setVerbosity(std::string option, int value) throw(OptionException);
  void increaseVerbosity(std::string option);
  void decreaseVerbosity(std::string option);
  OutputLanguage stringToOutputLanguage(std::string option, std::string optarg) throw(OptionException);
  InputLanguage stringToInputLanguage(std::string option, std::string optarg) throw(OptionException);
  void addTraceTag(std::string option, std::string optarg);
  void addDebugTag(std::string option, std::string optarg);
  void notifyPrintSuccess(std::string option);

 private:

  /* Helper utilities */
  static std::string suggestTags(char const* const* validTags, std::string inputTag,
                                 char const* const* additionalTags = NULL);

  /** Pointer to the containing Options object.*/
  Options* d_options;

  /* Help strings */
  static const std::string s_bitblastingModeHelp;
  static const std::string s_bvSatSolverHelp;
  static const std::string s_booleanTermConversionModeHelp;
  static const std::string s_bvSlicerModeHelp;
  static const std::string s_cegqiFairModeHelp;
  static const std::string s_decisionModeHelp;
  static const std::string s_instFormatHelp ;
  static const std::string s_instWhenHelp;
  static const std::string s_iteLiftQuantHelp;
  static const std::string s_literalMatchHelp;
  static const std::string s_macrosQuantHelp;
  static const std::string s_quantDSplitHelp;
  static const std::string s_quantRepHelp;
  static const std::string s_mbqiModeHelp;
  static const std::string s_modelFormatHelp;
  static const std::string s_prenexQuantModeHelp;
  static const std::string s_qcfModeHelp;
  static const std::string s_qcfWhenModeHelp;
  static const std::string s_simplificationHelp;
  static const std::string s_cegqiSingleInvHelp;
  static const std::string s_sygusInvTemplHelp;
  static const std::string s_termDbModeHelp;
  static const std::string s_theoryOfModeHelp;
  static const std::string s_triggerSelModeHelp;
  static const std::string s_triggerActiveSelModeHelp;
  static const std::string s_ufssModeHelp;
  static const std::string s_userPatModeHelp;
  static const std::string s_fmfBoundMinModeModeHelp;
  static const std::string s_errorSelectionRulesHelp;
  static const std::string s_arithPropagationModeHelp;
  static const std::string s_arithUnateLemmasHelp;

}; /* class OptionHandler */


}/* CVC4::options namespace */
}/* CVC4 namespace */

#endif /*  __CVC4__OPTIONS__OPTIONS_HANDLER_H */

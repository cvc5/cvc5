/*********************                                                        */
/*! \file options_handler.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andrew Reynolds, Liana Hadarean
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include "options/datatypes_modes.h"
#include "options/decision_mode.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/options.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/simplification_mode.h"
#include "options/sygus_out_mode.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

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

  // theory/arith/options_handlers.h
  ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option,
                                                  std::string optarg);
  ArithPropagationMode stringToArithPropagationMode(std::string option,
                                                    std::string optarg);
  ErrorSelectionRule stringToErrorSelectionRule(std::string option,
                                                std::string optarg);

  // theory/quantifiers/options_handlers.h
  theory::quantifiers::InstWhenMode stringToInstWhenMode(std::string option,
                                                         std::string optarg);
  void checkInstWhenMode(std::string option,
                         theory::quantifiers::InstWhenMode mode);
  theory::quantifiers::LiteralMatchMode stringToLiteralMatchMode(
      std::string option, std::string optarg);
  void checkLiteralMatchMode(std::string option,
                             theory::quantifiers::LiteralMatchMode mode);
  theory::quantifiers::MbqiMode stringToMbqiMode(std::string option,
                                                 std::string optarg);
  void checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode);
  theory::quantifiers::QcfWhenMode stringToQcfWhenMode(std::string option,
                                                       std::string optarg);
  theory::quantifiers::QcfMode stringToQcfMode(std::string option,
                                               std::string optarg);
  theory::quantifiers::UserPatMode stringToUserPatMode(std::string option,
                                                       std::string optarg);
  theory::quantifiers::TriggerSelMode stringToTriggerSelMode(
      std::string option, std::string optarg);
  theory::quantifiers::TriggerActiveSelMode stringToTriggerActiveSelMode(
      std::string option, std::string optarg);
  theory::quantifiers::PrenexQuantMode stringToPrenexQuantMode(
      std::string option, std::string optarg);
  theory::quantifiers::TermDbMode stringToTermDbMode(std::string option,
                                                     std::string optarg);
  theory::quantifiers::IteLiftQuantMode stringToIteLiftQuantMode(
      std::string option, std::string optarg);
  theory::quantifiers::CbqiBvIneqMode stringToCbqiBvIneqMode(
      std::string option, std::string optarg);
  theory::quantifiers::CegqiSingleInvMode stringToCegqiSingleInvMode(
      std::string option, std::string optarg);
  theory::quantifiers::CegisSampleMode stringToCegisSampleMode(
      std::string option, std::string optarg);
  theory::quantifiers::SygusInvTemplMode stringToSygusInvTemplMode(
      std::string option, std::string optarg);
  theory::quantifiers::MacrosQuantMode stringToMacrosQuantMode(
      std::string option, std::string optarg);
  theory::quantifiers::QuantDSplitMode stringToQuantDSplitMode(
      std::string option, std::string optarg);
  theory::quantifiers::QuantRepMode stringToQuantRepMode(std::string option,
                                                         std::string optarg);
  theory::quantifiers::FmfBoundMinMode stringToFmfBoundMinMode(
      std::string option, std::string optarg);
  theory::SygusFairMode stringToSygusFairMode(std::string option,
                                              std::string optarg);

  // theory/bv/options_handlers.h
  void abcEnabledBuild(std::string option, bool value);
  void abcEnabledBuild(std::string option, std::string value);
  void satSolverEnabledBuild(std::string option, bool value);
  void satSolverEnabledBuild(std::string option, std::string optarg);

  theory::bv::BitblastMode stringToBitblastMode(std::string option,
                                                std::string optarg);
  theory::bv::BvSlicerMode stringToBvSlicerMode(std::string option,
                                                std::string optarg);
  void setBitblastAig(std::string option, bool arg);

  theory::bv::SatSolverMode stringToSatSolver(std::string option,
                                              std::string optarg);

  // theory/uf/options_handlers.h
  theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg);

  // theory/options_handlers.h
  theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg);
  void notifyUseTheoryList(std::string option);
  std::string handleUseTheoryList(std::string option, std::string optarg);


  // printer/options_handlers.h
  ModelFormatMode stringToModelFormatMode(std::string option,
                                          std::string optarg);
  InstFormatMode stringToInstFormatMode(std::string option, std::string optarg);

  // decision/options_handlers.h
  decision::DecisionMode stringToDecisionMode(std::string option,
                                              std::string optarg);
  decision::DecisionWeightInternal stringToDecisionWeightInternal(
      std::string option, std::string optarg);

  /* smt/options_handlers.h */
  void notifyForceLogic(const std::string& option);

  /**
   * Throws a ModalException if this option is being set after final
   * initialization.
   */
  void notifyBeforeSearch(const std::string& option);
  void notifyDumpMode(std::string option);
  SimplificationMode stringToSimplificationMode(std::string option,
                                                std::string optarg);
  SygusSolutionOutMode stringToSygusSolutionOutMode(std::string option,
                                                    std::string optarg);
  void setProduceAssertions(std::string option, bool value);
  void proofEnabledBuild(std::string option, bool value);
  void LFSCEnabledBuild(std::string option, bool value);
  void notifyDumpToFile(std::string option);
  void notifySetRegularOutputChannel(std::string option);
  void notifySetDiagnosticOutputChannel(std::string option);
  std::string checkReplayFilename(std::string option, std::string optarg);
  void notifySetReplayLogFilename(std::string option);

  void statsEnabledBuild(std::string option, bool value);

  unsigned long tlimitHandler(std::string option, std::string optarg);
  unsigned long tlimitPerHandler(std::string option, std::string optarg);
  unsigned long rlimitHandler(std::string option, std::string optarg);
  unsigned long rlimitPerHandler(std::string option, std::string optarg);

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
  static const std::string s_sygusSolutionOutModeHelp;
  static const std::string s_cbqiBvIneqModeHelp;
  static const std::string s_cegqiSingleInvHelp;
  static const std::string s_cegisSampleHelp;
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

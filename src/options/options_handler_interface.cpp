/*********************                                                        */
/*! \file options_handler_interface.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Interface for custom handlers and predicates options.
 **
 ** Interface for custom handlers and predicates options.
 **/

#include "options/options_handler_interface.h"

#include <ostream>
#include <string>

#include "base/cvc4_assert.h"
#include "base/exception.h"
#include "base/modal_exception.h"
#include "options/arith_heuristic_pivot_rule.h"
#include "options/arith_propagation_mode.h"
#include "options/arith_unate_lemma_mode.h"
#include "options/boolean_term_conversion_mode.h"
#include "options/bv_bitblast_mode.h"
#include "options/decision_mode.h"
#include "options/language.h"
#include "options/option_exception.h"
#include "options/printer_modes.h"
#include "options/quantifiers_modes.h"
#include "options/simplification_mode.h"
#include "options/theoryof_mode.h"
#include "options/ufss_mode.h"

namespace CVC4 {
namespace options {

static const char* s_third_argument_warning =
    "We no longer support passing the third argument to the setting an option as NULL.";

// theory/arith/options_handlers.h
ArithUnateLemmaMode stringToArithUnateLemmaMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToArithUnateLemmaMode(option, optarg);
}
ArithPropagationMode stringToArithPropagationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToArithPropagationMode(option, optarg);
}
ErrorSelectionRule stringToErrorSelectionRule(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToErrorSelectionRule(option, optarg);
}

// theory/quantifiers/options_handlers.h
theory::quantifiers::InstWhenMode stringToInstWhenMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToInstWhenMode(option, optarg);
}
void checkInstWhenMode(std::string option, theory::quantifiers::InstWhenMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->checkInstWhenMode(option, mode);
}
theory::quantifiers::LiteralMatchMode stringToLiteralMatchMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToLiteralMatchMode(option, optarg);
}
void checkLiteralMatchMode(std::string option, theory::quantifiers::LiteralMatchMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->checkLiteralMatchMode(option, mode);
}
theory::quantifiers::MbqiMode stringToMbqiMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToMbqiMode(option, optarg);
}
void checkMbqiMode(std::string option, theory::quantifiers::MbqiMode mode,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->checkMbqiMode(option, mode);
}
theory::quantifiers::QcfWhenMode stringToQcfWhenMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToQcfWhenMode(option, optarg);
}
theory::quantifiers::QcfMode stringToQcfMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToQcfMode(option, optarg);
}
theory::quantifiers::UserPatMode stringToUserPatMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToUserPatMode(option, optarg);
}
theory::quantifiers::TriggerSelMode stringToTriggerSelMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToTriggerSelMode(option, optarg);
}
theory::quantifiers::PrenexQuantMode stringToPrenexQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToPrenexQuantMode(option, optarg);
}
theory::quantifiers::CegqiFairMode stringToCegqiFairMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToCegqiFairMode(option, optarg);
}
theory::quantifiers::TermDbMode stringToTermDbMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler-> stringToTermDbMode(option, optarg);
}
theory::quantifiers::IteLiftQuantMode stringToIteLiftQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToIteLiftQuantMode(option, optarg);
}
theory::quantifiers::SygusInvTemplMode stringToSygusInvTemplMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToSygusInvTemplMode(option, optarg);
}
theory::quantifiers::MacrosQuantMode stringToMacrosQuantMode(std::string option, std::string optarg,  OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToMacrosQuantMode(option, optarg);
}


// theory/bv/options_handlers.h
void abcEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->abcEnabledBuild(option, value);
}
void abcEnabledBuild(std::string option, std::string value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->abcEnabledBuild(option, value);
}
theory::bv::BitblastMode stringToBitblastMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToBitblastMode(option, optarg);
}
theory::bv::BvSlicerMode stringToBvSlicerMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToBvSlicerMode(option, optarg);
}
void setBitblastAig(std::string option, bool arg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setBitblastAig(option, arg);
}


// theory/booleans/options_handlers.h
theory::booleans::BooleanTermConversionMode stringToBooleanTermConversionMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToBooleanTermConversionMode( option, optarg);
}

// theory/uf/options_handlers.h
theory::uf::UfssMode stringToUfssMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToUfssMode(option, optarg);
}

// theory/options_handlers.h
theory::TheoryOfMode stringToTheoryOfMode(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToTheoryOfMode(option, optarg);
}
void useTheory(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->useTheory(option, optarg);
}

// printer/options_handlers.h
ModelFormatMode stringToModelFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToModelFormatMode(option, optarg);
}

InstFormatMode stringToInstFormatMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToInstFormatMode(option, optarg);
}


// decision/options_handlers.h
decision::DecisionMode stringToDecisionMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToDecisionMode(option, optarg);
}

decision::DecisionWeightInternal stringToDecisionWeightInternal(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToDecisionWeightInternal(option, optarg);
}


/* options/base_options_handlers.h */
void setVerbosity(std::string option, int value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setVerbosity(option, value);
}
void increaseVerbosity(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->increaseVerbosity(option);
}
void decreaseVerbosity(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->decreaseVerbosity(option);
}

OutputLanguage stringToOutputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToOutputLanguage(option, optarg);
}

InputLanguage stringToInputLanguage(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToInputLanguage(option, optarg);
}

void addTraceTag(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->addTraceTag(option, optarg);
}

void addDebugTag(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->addDebugTag(option, optarg);
}

void setPrintSuccess(std::string option, bool value, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setPrintSuccess(option, value);
}


/* main/options_handlers.h */
void showConfiguration(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->showConfiguration(option);
}

void showDebugTags(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->showDebugTags(option);
}

void showTraceTags(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->showTraceTags(option);
}

void threadN(std::string option, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->threadN(option);
}

/* expr/options_handlers.h */
void setDefaultExprDepth(std::string option, int depth, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setDefaultExprDepth(option, depth);
}

void setDefaultDagThresh(std::string option, int dag, OptionsHandler* handler){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setDefaultDagThresh(option, dag);
}

void setPrintExprTypes(std::string option, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setPrintExprTypes(option);
}


/* smt/options_handlers.h */
void dumpMode(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->dumpMode(option, optarg);
}

LogicInfo* stringToLogicInfo(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToLogicInfo(option, optarg);
}

SimplificationMode stringToSimplificationMode(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->stringToSimplificationMode(option, optarg);
}

// ensure we haven't started search yet
void beforeSearch(std::string option, bool value, OptionsHandler* handler) throw(ModalException){
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->beforeSearch(option, value);
}

void setProduceAssertions(std::string option, bool value, OptionsHandler* handler) throw() {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setProduceAssertions(option, value);
}

// ensure we are a proof-enabled build of CVC4
void proofEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->proofEnabledBuild(option, value);
}

void dumpToFile(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->dumpToFile(option, optarg);
}

void setRegularOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setRegularOutputChannel(option, optarg);
}

void setDiagnosticOutputChannel(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  handler->setDiagnosticOutputChannel(option, optarg);
}

std::string checkReplayFilename(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->checkReplayFilename(option, optarg);
}

std::ostream* checkReplayLogFilename(std::string option, std::string optarg, OptionsHandler* handler) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->checkReplayLogFilename(option, optarg);
}

// ensure we are a stats-enabled build of CVC4
void statsEnabledBuild(std::string option, bool value, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->statsEnabledBuild(option, value);
}

unsigned long tlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->tlimitHandler(option, optarg);
}

unsigned long tlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler-> tlimitPerHandler(option, optarg);
}

unsigned long rlimitHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->rlimitHandler(option, optarg);
}

unsigned long rlimitPerHandler(std::string option, std::string optarg, OptionsHandler* handler) throw(OptionException) {
  PrettyCheckArgument(handler != NULL, handler, s_third_argument_warning);
  return handler->rlimitPerHandler(option, optarg);
}



OptionsHandler::OptionsHandler() { }

}/* CVC4::options namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file options_public_functions.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definitions of public facing interface functions for Options.
 **
 ** Definitions of public facing interface functions for Options. These are
 ** all 1 line wrappers for Options::get<T>, Options::set<T>, and
 ** Options::wasSetByUser<T> for different option types T.
 **/

#include "options.h"

#include <fstream>
#include <ostream>
#include <string>
#include <vector>

#include "base/listener.h"
#include "base/modal_exception.h"
#include "options/base_options.h"
#include "options/language.h"
#include "options/main_options.h"
#include "options/option_exception.h"
#include "options/parser_options.h"
#include "options/printer_modes.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"

namespace CVC4 {

// Get accessor functions.
InputLanguage Options::getInputLanguage() const {
  return (*this)[options::inputLanguage];
}

options::InstFormatMode Options::getInstFormatMode() const
{
  return (*this)[options::instFormatMode];
}

OutputLanguage Options::getOutputLanguage() const {
  return (*this)[options::outputLanguage];
}

bool Options::getUfHo() const { return (*this)[options::ufHo]; }

bool Options::getCheckProofs() const{
  return (*this)[options::checkProofs];
}

bool Options::getDumpInstantiations() const{
  return (*this)[options::dumpInstantiations];
}

bool Options::getDumpModels() const{
  return (*this)[options::dumpModels];
}

bool Options::getDumpProofs() const{
  return (*this)[options::dumpProofs];
}

bool Options::getDumpSynth() const{
  return (*this)[options::dumpSynth];
}

bool Options::getDumpUnsatCores() const{
  return (*this)[options::dumpUnsatCores];
}

bool Options::getEarlyExit() const{
  return (*this)[options::earlyExit];
}

bool Options::getFilesystemAccess() const{
  return (*this)[options::filesystemAccess];
}

bool Options::getForceNoLimitCpuWhileDump() const{
  return (*this)[options::forceNoLimitCpuWhileDump];
}

bool Options::getHelp() const{
  return (*this)[options::help];
}

bool Options::getIncrementalSolving() const{
  return (*this)[options::incrementalSolving];
}

bool Options::getInteractive() const{
  return (*this)[options::interactive];
}

bool Options::getInteractivePrompt() const{
  return (*this)[options::interactivePrompt];
}

bool Options::getLanguageHelp() const{
  return (*this)[options::languageHelp];
}

bool Options::getMemoryMap() const{
  return (*this)[options::memoryMap];
}

bool Options::getParseOnly() const{
  return (*this)[options::parseOnly];
}

bool Options::getProduceModels() const{
  return (*this)[options::produceModels];
}

bool Options::getProof() const{
  return (*this)[options::proof];
}

bool Options::getSegvSpin() const{
  return (*this)[options::segvSpin];
}

bool Options::getSemanticChecks() const{
  return (*this)[options::semanticChecks];
}

bool Options::getStatistics() const{
  return (*this)[options::statistics];
}

bool Options::getStatsEveryQuery() const{
  return (*this)[options::statsEveryQuery];
}

bool Options::getStatsHideZeros() const{
  return (*this)[options::statsHideZeros];
}

bool Options::getStrictParsing() const{
  return (*this)[options::strictParsing];
}

int Options::getTearDownIncremental() const{
  return (*this)[options::tearDownIncremental];
}

bool Options::getVersion() const{
  return (*this)[options::version];
}

const std::string& Options::getForceLogicString() const{
  return (*this)[options::forceLogicString];
}

int Options::getVerbosity() const{
  return (*this)[options::verbosity];
}

std::istream* Options::getIn() const{
  return (*this)[options::in];
}

std::ostream* Options::getErr(){
  return (*this)[options::err];
}

std::ostream* Options::getOut(){
  return (*this)[options::out];
}

std::ostream* Options::getOutConst() const{
  // #warning "Remove Options::getOutConst"
  return (*this)[options::out];
}

std::string Options::getBinaryName() const{
  return (*this)[options::binary_name];
}

std::string Options::getReplayInputFilename() const{
  return (*this)[options::replayInputFilename];
}

unsigned Options::getParseStep() const{
  return (*this)[options::parseStep];
}

std::ostream* Options::currentGetOut() {
  return current()->getOut();
}


// TODO: Document these.

void Options::setInputLanguage(InputLanguage value) {
  set(options::inputLanguage, value);
}

void Options::setInteractive(bool value) {
  set(options::interactive, value);
}

void Options::setOut(std::ostream* value) {
  set(options::out, value);
}

void Options::setOutputLanguage(OutputLanguage value) {
  set(options::outputLanguage, value);
}

bool Options::wasSetByUserDumpSynth() const {
  return wasSetByUser(options::dumpSynth);
}

bool Options::wasSetByUserEarlyExit() const {
  return wasSetByUser(options::earlyExit);
}

bool Options::wasSetByUserForceLogicString() const {
  return wasSetByUser(options::forceLogicString);
}

bool Options::wasSetByUserIncrementalSolving() const {
  return wasSetByUser(options::incrementalSolving);
}

bool Options::wasSetByUserInteractive() const {
  return wasSetByUser(options::interactive);
}


void Options::flushErr() {
  if(getErr() != NULL) {
    *(getErr()) << std::flush;
  }
}

void Options::flushOut() {
  if(getOut() != NULL) {
    *(getOut()) << std::flush;
  }
}

}/* CVC4 namespace */

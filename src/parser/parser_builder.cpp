/*********************                                                        */
/*! \file parser_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A builder for parsers.
 **
 ** A builder for parsers.
 **/

// This must be included first.
#include "parser/antlr_input.h"

#include "parser/parser_builder.h"

#include <string>

#include "api/cvc4cpp.h"
#include "cvc/cvc.h"
#include "expr/expr_manager.h"
#include "options/options.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "smt2/smt2.h"
#include "tptp/tptp.h"

namespace CVC4 {
namespace parser {

ParserBuilder::ParserBuilder(api::Solver* solver, const std::string& filename)
    : d_filename(filename), d_solver(solver)
{
  init(solver, filename);
}

ParserBuilder::ParserBuilder(api::Solver* solver,
                             const std::string& filename,
                             const Options& options)
    : d_filename(filename), d_solver(solver)
{
  init(solver, filename);
  withOptions(options);
}

void ParserBuilder::init(api::Solver* solver, const std::string& filename)
{
  d_inputType = FILE_INPUT;
  d_lang = language::input::LANG_AUTO;
  d_filename = filename;
  d_streamInput = NULL;
  d_solver = solver;
  d_checksEnabled = true;
  d_strictMode = false;
  d_canIncludeFile = true;
  d_mmap = false;
  d_parseOnly = false;
  d_logicIsForced = false;
  d_forcedLogic = "";
}

Parser* ParserBuilder::build()
{
  Input* input = NULL;
  switch( d_inputType ) {
  case FILE_INPUT:
    input = Input::newFileInput(d_lang, d_filename, d_mmap);
    break;
  case LINE_BUFFERED_STREAM_INPUT:
    assert( d_streamInput != NULL );
    input = Input::newStreamInput(d_lang, *d_streamInput, d_filename, true);
    break;
  case STREAM_INPUT:
    assert( d_streamInput != NULL );
    input = Input::newStreamInput(d_lang, *d_streamInput, d_filename);
    break;
  case STRING_INPUT:
    input = Input::newStringInput(d_lang, d_stringInput, d_filename);
    break;
  }

  assert(input != NULL);

  Parser* parser = NULL;
  switch (d_lang)
  {
    case language::input::LANG_SYGUS_V2:
      parser = new Smt2(d_solver, input, d_strictMode, d_parseOnly);
      break;
    case language::input::LANG_TPTP:
      parser = new Tptp(d_solver, input, d_strictMode, d_parseOnly);
      break;
    default:
      if (language::isInputLang_smt2(d_lang))
      {
        parser = new Smt2(d_solver, input, d_strictMode, d_parseOnly);
      }
      else
      {
        parser = new Cvc(d_solver, input, d_strictMode, d_parseOnly);
      }
      break;
  }

  if( d_checksEnabled ) {
    parser->enableChecks();
  } else {
    parser->disableChecks();
  }

  if( d_canIncludeFile ) {
    parser->allowIncludeFile();
  } else {
    parser->disallowIncludeFile();
  }

  if( d_logicIsForced ) {
    parser->forceLogic(d_forcedLogic);
  }

  return parser;
}

ParserBuilder& ParserBuilder::withChecks(bool flag) {
  d_checksEnabled = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withSolver(api::Solver* solver)
{
  d_solver = solver;
  return *this;
}

ParserBuilder& ParserBuilder::withFileInput() {
  d_inputType = FILE_INPUT;
  return *this;
}

ParserBuilder& ParserBuilder::withFilename(const std::string& filename) {
  d_filename = filename;
  return *this;
}

ParserBuilder& ParserBuilder::withInputLanguage(InputLanguage lang) {
  d_lang = lang;
  return *this;
}

ParserBuilder& ParserBuilder::withMmap(bool flag) {
  d_mmap = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withParseOnly(bool flag) {
  d_parseOnly = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withOptions(const Options& options) {
  ParserBuilder& retval = *this;
  retval =
      retval.withInputLanguage(options.getInputLanguage())
      .withMmap(options.getMemoryMap())
      .withChecks(options.getSemanticChecks())
      .withStrictMode(options.getStrictParsing())
      .withParseOnly(options.getParseOnly())
      .withIncludeFile(options.getFilesystemAccess());
  if(options.wasSetByUserForceLogicString()) {
    LogicInfo tmp(options.getForceLogicString());
    retval = retval.withForcedLogic(tmp.getLogicString());
  }
  return retval;
}

ParserBuilder& ParserBuilder::withStrictMode(bool flag) {
  d_strictMode = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withIncludeFile(bool flag) {
  d_canIncludeFile = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withForcedLogic(const std::string& logic) {
  d_logicIsForced = true;
  d_forcedLogic = logic;
  return *this;
}

ParserBuilder& ParserBuilder::withStreamInput(std::istream& input) {
  d_inputType = STREAM_INPUT;
  d_streamInput = &input;
  return *this;
}

ParserBuilder& ParserBuilder::withLineBufferedStreamInput(std::istream& input) {
  d_inputType = LINE_BUFFERED_STREAM_INPUT;
  d_streamInput = &input;
  return *this;
}

ParserBuilder& ParserBuilder::withStringInput(const std::string& input) {
  d_inputType = STRING_INPUT;
  d_stringInput = input;
  return *this;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

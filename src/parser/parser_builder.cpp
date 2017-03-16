/*********************                                                        */
/*! \file parser_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "options/options.h"
#include "smt1/smt1.h"
#include "smt2/smt2.h"
#include "tptp/tptp.h"

namespace CVC4 {
namespace parser {

ParserBuilder::ParserBuilder(ExprManager* exprManager,
                             const std::string& filename) :
  d_filename(filename),
  d_exprManager(exprManager) {
  init(exprManager, filename);
}

ParserBuilder::ParserBuilder(ExprManager* exprManager,
                             const std::string& filename,
                             const Options& options) :
  d_filename(filename),
  d_exprManager(exprManager) {
  init(exprManager, filename);
  withOptions(options);
}

void ParserBuilder::init(ExprManager* exprManager,
                         const std::string& filename) {
  d_inputType = FILE_INPUT;
  d_lang = language::input::LANG_AUTO;
  d_filename = filename;
  d_streamInput = NULL;
  d_exprManager = exprManager;
  d_checksEnabled = true;
  d_strictMode = false;
  d_canIncludeFile = true;
  d_mmap = false;
  d_parseOnly = false;
  d_logicIsForced = false;
  d_forcedLogic = "";
}

Parser* ParserBuilder::build()
  throw (InputStreamException) {
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
  switch(d_lang) {
  case language::input::LANG_SMTLIB_V1:
    parser = new Smt1(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  case language::input::LANG_SMTLIB_V2_0:
  case language::input::LANG_SMTLIB_V2_5:
  case language::input::LANG_SMTLIB_V2_6:
    parser = new Smt2(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  case language::input::LANG_SYGUS:
    parser = new Smt2(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  case language::input::LANG_TPTP:
    parser = new Tptp(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  default:
    parser = new Parser(d_exprManager, input, d_strictMode, d_parseOnly);
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

ParserBuilder& ParserBuilder::withExprManager(ExprManager* exprManager) {
  d_exprManager = exprManager;
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

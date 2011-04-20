/*********************                                                        */
/*! \file parser_builder.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A builder for parsers.
 **
 ** A builder for parsers.
 **/

#include <string>

#include "parser_builder.h"
#include "input.h"
#include "parser.h"
#include "smt/smt.h"
#include "smt2/smt2.h"

#include "expr/expr_manager.h"
#include "util/options.h"

namespace CVC4 {

namespace parser {

ParserBuilder::ParserBuilder(ExprManager* exprManager, 
                             const std::string& filename) : 
  d_filename(filename),
  d_exprManager(exprManager) {
  init(exprManager,filename);
}

ParserBuilder::ParserBuilder(ExprManager* exprManager, 
                             const std::string& filename, 
                             const Options& options) :
  d_filename(filename),
  d_exprManager(exprManager) {
  init(exprManager,filename);
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
  d_mmap = false;
  d_parseOnly = false;
}

Parser *ParserBuilder::build() 
  throw (InputStreamException,AssertionException) {
  Input *input = NULL;
  switch( d_inputType ) {
  case FILE_INPUT:
    input = Input::newFileInput(d_lang,d_filename,d_mmap);
    break;
  case STREAM_INPUT:
    AlwaysAssert( d_streamInput != NULL,
                  "Uninitialized stream input in ParserBuilder::build()" );
    input = Input::newStreamInput(d_lang,*d_streamInput,d_filename);
    break;
  case STRING_INPUT:
    input = Input::newStringInput(d_lang,d_stringInput,d_filename);
    break;
  default:
    Unreachable();
  }

  Parser *parser = NULL;
  switch(d_lang) {
  case language::input::LANG_SMTLIB:
    parser = new Smt(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  case language::input::LANG_SMTLIB_V2:
    parser = new Smt2(d_exprManager, input, d_strictMode, d_parseOnly);
    break;
  default:
    parser = new Parser(d_exprManager, input, d_strictMode, d_parseOnly);
  }

  if( d_checksEnabled ) {
    parser->enableChecks();
  } else {
    parser->disableChecks();
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
  return
    withInputLanguage(options.inputLanguage)
      .withMmap(options.memoryMap)
      .withChecks(options.semanticChecks)
      .withStrictMode(options.strictParsing)
      .withParseOnly(options.parseOnly);
  }

ParserBuilder& ParserBuilder::withStrictMode(bool flag) {
  d_strictMode = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withStreamInput(std::istream& input) {
  d_inputType = STREAM_INPUT;
  d_streamInput = &input;
  return *this;
}

ParserBuilder& ParserBuilder::withStringInput(const std::string& input) {
  d_inputType = STRING_INPUT;
  d_stringInput = input;
  return *this;
}

} /* namespace parser */

} /* namespace CVC4 */

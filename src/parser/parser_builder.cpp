/*********************                                                        */
/** parser_builder.cpp
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A builder for parsers.
 **/

#include <string>

#include "parser_builder.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/parser.h"
#include "parser/smt2/smt2.h"

namespace CVC4 {

namespace parser {

/*class FileInputBuilder : public InputBuilder {
  bool d_useMmap;
public:
  FileInputBuilder(InputLanguage lang, const std::string& filename, bool useMmap) :
    InputBuilder(lang,filename),
    d_useMmap(useMmap) {
  }
  ParserBuilder& useMmap();

  Input& build() {
    return Input::newFileInput(d_lang,d_name,d_useMmap);
  }
};

class StringInputBuilder : public InputBuilder {
  std::string d_input;
public:
  StringInputBuilder(InputLanguage lang, const std::string& input, const std::string& name) :
    InputBuilder(lang,name),
    d_input(input) {
  }

  Input& build() {
    return Input::newStringInput(lang,input,name);
  }
};*/

ParserBuilder::ParserBuilder(InputLanguage lang, const std::string& filename) :
    d_inputType(FILE_INPUT),
    d_lang(lang),
    d_filename(filename),
    d_exprManager(NULL),
    d_checksEnabled(true),
    d_strictMode(false),
    d_mmap(false) {
}

Parser *ParserBuilder::build() throw (InputStreamException) {
  Input *input;
  switch( d_inputType ) {
  case FILE_INPUT:
    input = Input::newFileInput(d_lang,d_filename,d_mmap);
    break;
  case STRING_INPUT:
    input = Input::newStringInput(d_lang,d_stringInput,d_filename);
    break;
  }
  switch(d_lang) {
  case LANG_SMTLIB_V2:
    return new Smt2(d_exprManager, input, d_strictMode);
  default:
    return new Parser(d_exprManager, input, d_strictMode);
  }
}

/*ParserBuilder& ParserBuilder::disableChecks() {
  d_checksEnabled = false;
  return *this;
}

ParserBuilder& ParserBuilder::disableMmap() {
  d_mmap = false;
  return *this;
}

ParserBuilder& ParserBuilder::disableStrictMode() {
  d_strictMode = false;
  return *this;
}

ParserBuilder& ParserBuilder::enableChecks() {
  d_checksEnabled = true;
  return *this;
}

ParserBuilder& ParserBuilder::enableMmap() {
  d_mmap = true;
  return *this;
}

ParserBuilder& ParserBuilder::enableStrictMode() {
  d_strictMode = true;
  return *this;
}*/

ParserBuilder& ParserBuilder::withChecks(bool flag) {
  d_checksEnabled = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withMmap(bool flag) {
  d_mmap = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withStrictMode(bool flag) {
  d_strictMode = flag;
  return *this;
}

ParserBuilder& ParserBuilder::withExprManager(ExprManager& exprManager) {
  d_exprManager = &exprManager;
  return *this;
}

ParserBuilder& ParserBuilder::withStringInput(const std::string& input) {
  d_inputType = STRING_INPUT;
  d_stringInput = input;
  return *this;
}

} /* namespace parser */

} /* namespace CVC4 */

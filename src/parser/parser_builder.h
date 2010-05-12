/*********************                                                        */
/** parser_builder.h
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

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_BUILDER_H_
#define __CVC4__PARSER__PARSER_BUILDER_H_

#include <string>

#include "parser/input.h"
#include "parser/parser_options.h"

namespace CVC4 {

class ExprManager;

namespace parser {
/*

class InputBuilder {
protected:
  InputLanguage d_lang;
  std::string d_name;
public:
  InputBuilder(InputLanguage lang, const std::string& name) :
    d_lang(lang),
    d_name(name) {
  }
  virtual Input& build() = 0;
};
*/

class Parser;

class CVC4_PUBLIC ParserBuilder {
  enum InputType {
    FILE_INPUT,
    STRING_INPUT
  };

  /** The input type. */
  InputType d_inputType;

  /** The input language */
  InputLanguage d_lang;

  /** The file name (may not exist) */
  std::string d_filename;

  /** The string input, if any. */
  std::string d_stringInput;

  /** The expression manager */
  ExprManager *d_exprManager;

  /** Should semantic checks be enabled during parsing? */
  bool d_checksEnabled;

  /** Should we parse in strict mode? */
  bool d_strictMode;

  /** Should we memory-map a file input? */
  bool d_mmap;

public:
  ParserBuilder(InputLanguage lang, const std::string& filename);
  Parser *build() throw (InputStreamException);
  ParserBuilder& withChecks(bool flag = true);
  ParserBuilder& withMmap(bool flag = true);
  ParserBuilder& withStrictMode(bool flag = true);
  ParserBuilder& withExprManager(ExprManager& exprManager);
  ParserBuilder& withStringInput(const std::string& input);
};

} /* namespace parser */

} /* namespace CVC4 */
#endif /* __CVC4__PARSER__PARSER_BUILDER_H_ */

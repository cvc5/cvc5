/*********************                                                        */
/*! \file parser_builder.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A builder for parsers.
 **
 ** A builder for parsers.
 **/

#include "cvc4parser_public.h"

#ifndef __CVC4__PARSER__PARSER_BUILDER_H
#define __CVC4__PARSER__PARSER_BUILDER_H

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

/**
 * A builder for input language parsers. <code>build()</code> can be
 * called any number of times on an instance and will generate a fresh
 * parser each time.
 */
class CVC4_PUBLIC ParserBuilder {
  enum InputType {
    FILE_INPUT,
    STREAM_INPUT,
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

  /** The stream input, if any. */
  std::istream *d_streamInput;

  /** The expression manager */
  ExprManager& d_exprManager;

  /** Should semantic checks be enabled during parsing? */
  bool d_checksEnabled;

  /** Should we parse in strict mode? */
  bool d_strictMode;

  /** Should we memory-map a file input? */
  bool d_mmap;

public:

  /** Create a parser builder using the given ExprManager and filename. */
  ParserBuilder(ExprManager& exprManager, const std::string& filename);

  /** Build the parser, using the current settings. */
  Parser *build() throw (InputStreamException,AssertionException);

  /** Should semantic checks be enabled in the parser? (Default: yes) */
  ParserBuilder& withChecks(bool flag = true);

  /** Set the ExprManager to use with the parser. */
  ParserBuilder& withExprManager(ExprManager& exprManager);

  /** Set the parser to read a file for its input. (Default) */
  ParserBuilder& withFileInput();

  /** Set the filename for use by the parser. If file input is used,
   * this file will be opened and read by the parser. Otherwise, the
   * filename string (possibly a non-existent path) will only be used
   * in error messages. */
  ParserBuilder& withFilename(const std::string& filename);

  /** Set the input language to be used by the parser. (Default:
      LANG_AUTO). */
  ParserBuilder& withInputLanguage(InputLanguage lang);

  /** Should the parser memory-map its input? This is only relevant if
   * the parser will have a file input. (Default: no) */
  ParserBuilder& withMmap(bool flag = true);

  /** Should the parser use strict mode? (Default: no) */
  ParserBuilder& withStrictMode(bool flag = true);

  /** Set the parser to use the given stream for its input. */
  ParserBuilder& withStreamInput(std::istream& input);

  /** Set the parser to use the given string for its input. */
  ParserBuilder& withStringInput(const std::string& input);
};/* class ParserBuilder */

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_BUILDER_H */

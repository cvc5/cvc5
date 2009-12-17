/*********************                                           -*- C++ -*-  */
/** smt_parser.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): cconway, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** SMT-LIB language parser abstraction.
 **/

#ifndef __CVC4__PARSER__SMT_PARSER_H
#define __CVC4__PARSER__SMT_PARSER_H

#include <string>
#include <iostream>
#include <fstream>
#include "cvc4_config.h"
#include "parser/parser_exception.h"
#include "parser/parser.h"

namespace CVC4 {
namespace parser {

/**
 * The SMT parser.
 */
class CVC4_PUBLIC SmtParser : public Parser {

public:

  /**
   * Construct the parser that uses the given expression manager and input stream.
   * @param em the expression manager to use
   * @param input the input stream to parse
   * @param file_name the name of the file (for diagnostic output)
   */
  SmtParser(ExprManager* em, std::istream& input, const char* file_name = "");

  /**
   * Destructor.
   */
  ~SmtParser();

  /**
   * Parses the next command. By default, the SMT-LIB parser produces
   * one CommandSequence command. If parsing is successful, we should
   * be done after the first call to this command.
   * @return the CommandSequence command that includes the whole
   * benchmark
   */
  Command* parseNextCommand() throw(ParserException);

  /**
   * Parses the next complete expression of the stream.
   * @return the expression parsed
   */
  Expr parseNextExpression() throw(ParserException);

protected:

  /** The ANTLR smt lexer */
  AntlrSmtLexer* d_antlr_lexer;

  /** The ANTLR smt parser */
  AntlrSmtParser* d_antlr_parser;

  /** The file stream we might be using */
  std::istream& d_input;
};

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__SMT_PARSER_H */

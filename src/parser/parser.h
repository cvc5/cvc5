/*********************                                                        */
/** parser.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser abstraction.
 **/

#ifndef __CVC4__PARSER__PARSER_H
#define __CVC4__PARSER__PARSER_H

#include <string>
#include <iostream>

#include "cvc4_config.h"
#include "parser/parser_exception.h"
#include "util/Assert.h"

namespace antlr {
  class CharScanner;
  class InputBuffer;
}

namespace CVC4 {

// Forward declarations
class Expr;
class Command;
class ExprManager;

namespace parser {

class AntlrParser;

/**
 * The parser. The parser should be obtained by calling the static methods
 * getNewParser, and should be deleted when done.
 */
class CVC4_PUBLIC Parser {

public:

  /** The input language option */
  enum InputLanguage {
    /** The SMTLIB input language */
    LANG_SMTLIB,
    /** The CVC4 input language */
    LANG_CVC4,
    /** Auto-detect the language */
    LANG_AUTO
  };

  static Parser* getMemoryMappedParser(ExprManager* em, InputLanguage lang, std::string filename);
  static Parser* getNewParser(ExprManager* em, InputLanguage lang, std::istream& input, std::string filename);

  /**
   * Destructor.
   */
  ~Parser();

  /**
   * Parse the next command of the input. If EOF is encountered a EmptyCommand
   * is returned and done flag is set.
   */
  Command* parseNextCommand() throw(ParserException, AssertionException);

  /**
   * Parse the next expression of the stream. If EOF is encountered a null
   * expression is returned and done flag is set.
   * @return the parsed expression
   */
  Expr parseNextExpression() throw(ParserException, AssertionException);

  /**
   * Check if we are done -- either the end of input has been reached, or some
   * error has been encountered.
   * @return true if parser is done
   */
  bool done() const;

  /** Enable semantic checks during parsing. */
  void enableChecks();

  /** Disable semantic checks during parsing. Disabling checks may lead to crashes on bad inputs. */
  void disableChecks();

private:

  /**
   * Create a new parser.
   * @param em the expression manager to usee
   * @param lang the language to parse
   * @param inputBuffer the input buffer to parse
   * @param filename the filename to attach to the stream
   * @param deleteInput wheather to delete the input
   * @return the parser
   */
  static Parser* getNewParser(ExprManager* em, InputLanguage lang, antlr::InputBuffer* inputBuffer, std::string filename);

  /**
   * Create a new parser given the actual antlr parser.
   * @param antlrParser the antlr parser to user
   */
  Parser(antlr::InputBuffer* inputBuffer, AntlrParser* antlrParser, antlr::CharScanner* antlrLexer);

  /** Sets the done flag */
  void setDone(bool done = true);

  /** Are we done */
  bool d_done;

  /** The antlr parser */
  AntlrParser* d_antlrParser;

  /** The entlr lexer */
  antlr::CharScanner* d_antlrLexer;

  /** The input stream we are using */
  antlr::InputBuffer* d_inputBuffer;

  /** Wherther to de-allocate the input */
  bool d_deleteInput;
}; // end of class Parser

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__PARSER_H */

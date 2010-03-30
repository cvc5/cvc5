/*********************                                                        */
/** antlr_parser.h
 ** Original author: dejan
 ** Major contributors: cconway
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Base for ANTLR parser classes.
 **/

#include "cvc4parser_private.h"

#ifndef __CVC4__PARSER__ANTLR_PARSER_H
#define __CVC4__PARSER__ANTLR_PARSER_H

#include <vector>
#include <string>
#include <iostream>
#include <antlr3.h>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "parser/input.h"
#include "parser/symbol_table.h"
#include "util/Assert.h"

namespace CVC4 {

class Command;
class Type;
class FunctionType;

namespace parser {

/**
 * Wrapper for an ANTLR parser that includes convenience methods to set up input and token streams.
 */
class AntlrInput : public Input {

  unsigned int d_lookahead;
  pANTLR3_LEXER d_lexer;
  pANTLR3_PARSER d_parser;
  pANTLR3_COMMON_TOKEN_STREAM d_tokenStream;
  pANTLR3_INPUT_STREAM d_input;

  static void reportError(pANTLR3_BASE_RECOGNIZER recognizer);

public:
  AntlrInput(ExprManager* exprManager, const std::string& filename, unsigned int lookahead, bool useMmap);
  // AntlrParser(ExprManager* em, std::istream& input, const std::string& name, unsigned int lookahead);
  AntlrInput(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead);
  ~AntlrInput();

  inline static std::string tokenText(pANTLR3_COMMON_TOKEN token);

protected:

  /**
   * Throws a semantic exception with the given message.
   */
  void parseError(const std::string& msg) throw (ParserException);

  /** Get the lexer */
  pANTLR3_LEXER getLexer();
  /** Retrieve the input stream for this parser. */
  pANTLR3_INPUT_STREAM getInputStream();
  /** Retrieve the token stream for this parser. Must not be called before <code>setLexer()</code>. */
  pANTLR3_COMMON_TOKEN_STREAM getTokenStream();
  /** Set the ANTLR lexer for this parser. */
  void setLexer(pANTLR3_LEXER pLexer);
  /** Set the ANTLR parser implementation for this parser. */
  void setParser(pANTLR3_PARSER pParser);
};

std::string AntlrInput::tokenText(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  ANTLR3_MARKER end = token->getStopIndex(token);
  std::string txt( (const char *)start, end-start+1 );
  Debug("parser-extra") << "tokenText: start=" << start << std::endl
                        <<  "end=" << end << std::endl
                        <<  "txt='" << txt << "'" << std::endl;
  return txt;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_PARSER_H */

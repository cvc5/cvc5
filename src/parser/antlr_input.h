/*********************                                                        */
/** antlr_input.h
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
  /** The token lookahead used to lex and parse the input. This should usually be equal to
   * <code>K</code> for an LL(k) grammar. */
  unsigned int d_lookahead;

  /** The ANTLR3 lexer associated with this input. This will be <code>NULL</code> initially. It
   *  must be set by a call to <code>setLexer</code>, preferably in the subclass constructor. */
  pANTLR3_LEXER d_lexer;

  /** The ANTLR3 parser associated with this input. This will be <code>NULL</code> initially. It
   *  must be set by a call to <code>setParser</code>, preferably in the subclass constructor.
   *  The <code>super</code> field of <code>d_parser</code> will be set to <code>this</code> and
   *  <code>reportError</code> will be set to <code>AntlrInput::reportError</code>. */
  pANTLR3_PARSER d_parser;

  /** The ANTLR3 token stream associated with this input. We only need this so we can free it on exit.
   *  This is set by <code>setLexer</code>.
   *  NOTE: We assume that we <em>can</em> free it on exit. No sharing! */
  pANTLR3_COMMON_TOKEN_STREAM d_tokenStream;

  /** The ANTLR3 token stream associated with this input. We only need this so we can free it on exit.
   *  NOTE: We assume that we <em>can</em> free it on exit. No sharing! */
  pANTLR3_INPUT_STREAM d_input;

  /** Turns an ANTLR3 exception into a message for the user and calls <code>parseError</code>. */
  static void reportError(pANTLR3_BASE_RECOGNIZER recognizer);

public:

  /** Create a file input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param filename the path of the file to read
   * @param lookahead the lookahead needed to parse the input (i.e., k for an LL(k) grammar)
   * @param useMmap <code>true</code> if the input should use memory-mapped I/O; otherwise, the
   * input will use the standard ANTLR3 I/O implementation.
   */
  AntlrInput(ExprManager* exprManager, const std::string& filename, unsigned int lookahead, bool useMmap);

  /** Create an input from an istream. */
  // AntlrParser(ExprManager* em, std::istream& input, const std::string& name, unsigned int lookahead);

  /** Create a string input.
   *
   * @param exprManager the manager to use when building expressions from the input
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   * @param lookahead the lookahead needed to parse the input (i.e., k for an LL(k) grammar)
   */
  AntlrInput(ExprManager* exprManager, const std::string& input, const std::string& name, unsigned int lookahead);

  /** Destructor. Frees the token stream and closes the input. */
  ~AntlrInput();

  /** Retrieve the text associated with a token. */
  inline static std::string tokenText(pANTLR3_COMMON_TOKEN token);

protected:

  /**
   * Throws a <code>ParserException</code> with the given message.
   */
  void parseError(const std::string& msg) throw (ParserException);

  /** Retrieve the input stream for this parser. */
  pANTLR3_INPUT_STREAM getInputStream();
  /** Retrieve the token stream for this parser. Must not be called before
   * <code>setLexer()</code>. */
  pANTLR3_COMMON_TOKEN_STREAM getTokenStream();

  /** Set the ANTLR lexer for this parser. */
  void setLexer(pANTLR3_LEXER pLexer);

  /** Set the ANTLR parser implementation for this parser. */
  void setParser(pANTLR3_PARSER pParser);
};

std::string AntlrInput::tokenText(pANTLR3_COMMON_TOKEN token) {
  ANTLR3_MARKER start = token->getStartIndex(token);
  ANTLR3_MARKER end = token->getStopIndex(token);
  /* start and end are boundary pointers. The text is a string
   * of (end-start+1) bytes beginning at start. */
  std::string txt( (const char *)start, end-start+1 );
  Debug("parser-extra") << "tokenText: start=" << start << std::endl
                        <<  "end=" << end << std::endl
                        <<  "txt='" << txt << "'" << std::endl;
  return txt;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_PARSER_H */

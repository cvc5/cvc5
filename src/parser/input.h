/*********************                                                        */
/** input.h
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

#ifndef __CVC4__PARSER__ANTLR_INPUT_H
#define __CVC4__PARSER__ANTLR_INPUT_H

#include <antlr3.h>
#include <iostream>
#include <string>
#include <vector>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "parser/parser_exception.h"
#include "parser/parser_options.h"
#include "util/Assert.h"

namespace CVC4 {

class Command;
class Type;
class FunctionType;

namespace parser {

/** Wrapper around an ANTLR3 input stream. */
class AntlrInputStream {
  std::string d_name;
  pANTLR3_INPUT_STREAM d_input;

  AntlrInputStream(std::string name,pANTLR3_INPUT_STREAM input);
  /* This is private and throws an exception, because you should never use it. */
  AntlrInputStream(const AntlrInputStream& inputStream) {
    Unimplemented("copy constructor for AntlrInputStream");
  }
  /* This is private and throws an exception, because you should never use it. */
  AntlrInputStream& operator=(const AntlrInputStream& inputStream) {
    Unimplemented("operator= for AntlrInputStream");
  }

public:

  virtual ~AntlrInputStream();

  pANTLR3_INPUT_STREAM getAntlr3InputStream() const;
  const std::string getName() const;

  /** Create a file input.
   *
   * @param filename the path of the file to read
   * @param useMmap <code>true</code> if the input should use memory-mapped I/O; otherwise, the
   * input will use the standard ANTLR3 I/O implementation.
   */
  static AntlrInputStream* newFileInputStream(const std::string& name, bool useMmap = false);

  /** Create an input from an istream. */
  // AntlrInputStream newInputStream(std::istream& input, const std::string& name);

  /** Create a string input.
   *
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   */
  static AntlrInputStream* newStringInputStream(const std::string& input, const std::string& name);
};

class Parser;

/**
 * An input to be parsed. The static factory methods in this class (e.g.,
 * <code>newFileInput</code>, <code>newStringInput</code>) create a parser
 * for the given input language and attach it to an input source of the
 * appropriate type.
 */
class CVC4_PUBLIC Input {
  friend class Parser; // for parseError, parseCommand, parseExpr

  /** The display name of the input (e.g., the filename). */
  std::string d_name;

  /** The token lookahead used to lex and parse the input. This should usually be equal to
   * <code>K</code> for an LL(k) grammar. */
  unsigned int d_lookahead;

  /** The ANTLR3 lexer associated with this input. This will be <code>NULL</code> initially. It
   *  must be set by a call to <code>setLexer</code>, preferably in the subclass constructor. */
  pANTLR3_LEXER d_lexer;

  /** The ANTLR3 parser associated with this input. This will be <code>NULL</code> initially. It
   *  must be set by a call to <code>setParser</code>, preferably in the subclass constructor.
   *  The <code>super</code> field of <code>d_parser</code> will be set to <code>this</code> and
   *  <code>reportError</code> will be set to <code>Input::reportError</code>. */
  pANTLR3_PARSER d_parser;

  /** The ANTLR3 token stream associated with this input. We only need this so we can free it on exit.
   *  This is set by <code>setLexer</code>.
   *  NOTE: We assume that we <em>can</em> free it on exit. No sharing! */
  pANTLR3_COMMON_TOKEN_STREAM d_tokenStream;

  /** The ANTLR3 input stream associated with this input. We only need this so we can free it on exit.
   *  NOTE: We assume that we <em>can</em> free it on exit. No sharing! */
  AntlrInputStream *d_inputStream;

  /** Turns an ANTLR3 exception into a message for the user and calls <code>parseError</code>. */
  static void reportError(pANTLR3_BASE_RECOGNIZER recognizer);

  /** Builds a message for a lexer error and calls <code>parseError</code>. */
  static void lexerError(pANTLR3_BASE_RECOGNIZER recognizer);

  /* Since we own d_tokenStream and it needs to be freed, we need to prevent
   * copy construction and assignment.
   */
  Input(const Input& input) { Unimplemented("Copy constructor for Input."); }
  Input& operator=(const Input& input) { Unimplemented("operator= for Input."); }

public:

  /** Destructor. Frees the token stream and closes the input. */
  virtual ~Input();

  /** Create an input for the given file.
    *
    * @param lang the input language
    * @param filename the input filename
    * @param useMmap true if the parser should use memory-mapped I/O (default: false)
    */
  static Input* newFileInput(InputLanguage lang, const std::string& filename, bool useMmap=false);

  /** Create an input for the given AntlrInputStream. NOTE: the new Input
   * will take ownership of the input stream and delete it at destruction time.
   *
   * @param lang the input language
   * @param inputStream the input stream
   *
   * */
  static Input* newInput(InputLanguage lang, AntlrInputStream *inputStream);

  /** Create an input for the given stream.
   *
   * @param lang the input language
   * @param input the input stream
   * @param name the name of the stream, for use in error messages
   */
  //static Parser* newStreamInput(InputLanguage lang, std::istream& input, const std::string& name);

  /** Create an input for the given string
   *
   * @param lang the input language
   * @param input the input string
   * @param name the name of the stream, for use in error messages
   */
  static Input* newStringInput(InputLanguage lang, const std::string& input, const std::string& name);

  /** Retrieve the text associated with a token. */
  inline static std::string tokenText(pANTLR3_COMMON_TOKEN token);
  /** Retrieve an Integer from the text of a token */
  inline static Integer tokenToInteger( pANTLR3_COMMON_TOKEN token );
  /** Retrieve a Rational from the text of a token */
  inline static Rational tokenToRational(pANTLR3_COMMON_TOKEN token);

protected:
  /** Create an input. This input takes ownership of the given input stream,
   * and will delete it at destruction time.
   *
   * @param inputStream the input stream to use
   * @param lookahead the lookahead needed to parse the input (i.e., k for
   * an LL(k) grammar)
   */
  Input(AntlrInputStream *inputStream, unsigned int lookahead);


  /** Retrieve the input stream for this parser. */
  AntlrInputStream *getInputStream();

  /** Retrieve the token stream for this parser. Must not be called before
   * <code>setLexer()</code>. */
  pANTLR3_COMMON_TOKEN_STREAM getTokenStream();

  /** Parse a command from
   * the input by invoking the implementation-specific parsing method.  Returns
   * <code>NULL</code> if there is no command there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Command* parseCommand() throw(ParserException) = 0;

  /**
   * Throws a <code>ParserException</code> with the given message.
   */
  void parseError(const std::string& msg) throw (ParserException);

  /** Parse an
   * expression from the input by invoking the implementation-specific
   * parsing method. Returns a null <code>Expr</code> if there is no
   * expression there to parse.
   *
   * @throws ParserException if an error is encountered during parsing.
   */
  virtual Expr parseExpr() throw(ParserException) = 0;

  /** Set the ANTLR3 lexer for this input. */
  void setAntlr3Lexer(pANTLR3_LEXER pLexer);

  /** Set the ANTLR3 parser implementation for this input. */
  void setAntlr3Parser(pANTLR3_PARSER pParser);

  /** Set the Parser object for this input. */
  void setParser(Parser *parser);
};

std::string Input::tokenText(pANTLR3_COMMON_TOKEN token) {
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

Integer Input::tokenToInteger(pANTLR3_COMMON_TOKEN token) {
  Integer i( tokenText(token) );
  return i;
}

Rational Input::tokenToRational(pANTLR3_COMMON_TOKEN token) {
  Rational r( tokenText(token) );
  return r;
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* __CVC4__PARSER__ANTLR_INPUT_H */

/*********************                                                        */
/*! \file antlr_input.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Christopher L. Conway, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base for ANTLR parser classes.
 **
 ** Base for ANTLR parser classes.
 **/

#ifndef CVC4__PARSER__ANTLR_INPUT_H
#define CVC4__PARSER__ANTLR_INPUT_H

#include "cvc4parser_private.h"

#include <antlr3.h>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <cassert>

#include "base/output.h"
#include "parser/bounded_token_buffer.h"
#include "parser/input.h"
#include "parser/line_buffer.h"
#include "parser/parser_exception.h"
#include "util/bitvector.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {

class Command;
class Type;
class FunctionType;

namespace parser {

/** Wrapper around an ANTLR3 input stream. */
class AntlrInputStream : public InputStream {
private:
  pANTLR3_INPUT_STREAM d_input;

  /**
   * If the AntlrInputStream corresponds to reading from a string,
   * this is the string literal. The memory is owned by the Antlr3Input. It is
   * assumed to be copied from malloc, and can be free'd at destruction time.
   * It is otherwise NULL.
   */
  pANTLR3_UINT8 d_inputString;

  LineBuffer* d_line_buffer;

  AntlrInputStream(std::string name, pANTLR3_INPUT_STREAM input,
                   bool fileIsTemporary, pANTLR3_UINT8 inputString,
                   LineBuffer* line_buffer);

  /* This is private and unimplemented, because you should never use it. */
  AntlrInputStream(const AntlrInputStream& inputStream) = delete;

  /* This is private and unimplemented, because you should never use it. */
  AntlrInputStream& operator=(const AntlrInputStream& inputStream) = delete;

public:

  virtual ~AntlrInputStream();

  pANTLR3_INPUT_STREAM getAntlr3InputStream() const;

  /** Create a file input.
   *
   * @param name the path of the file to read
   * @param useMmap <code>true</code> if the input should use memory-mapped I/O; otherwise, the
   * input will use the standard ANTLR3 I/O implementation.
   */
  static AntlrInputStream* newFileInputStream(const std::string& name,
                                              bool useMmap = false);

  /** Create an input from an istream. */
  static AntlrInputStream* newStreamInputStream(std::istream& input,
                                                const std::string& name,
                                                bool lineBuffered = false);

  /** Create a string input.
   * NOTE: the new AntlrInputStream will take ownership of input over
   * and free it at destruction time.
   *
   * @param input the string to read
   * @param name the "filename" to use when reporting errors
   */
  static AntlrInputStream* newStringInputStream(const std::string& input,
                                                const std::string& name);
};/* class AntlrInputStream */

class Parser;

/**
 * An input to be parsed. The static factory methods in this class (e.g.,
 * <code>newFileInput</code>, <code>newStringInput</code>) create a parser
 * for the given input language and attach it to an input source of the
 * appropriate type.
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
   *  <code>reportError</code> will be set to <code>Input::reportError</code>. */
  pANTLR3_PARSER d_parser;

  /** The ANTLR3 input stream associated with this input. */
  pANTLR3_INPUT_STREAM d_antlr3InputStream;

  /** The ANTLR3 bounded token buffer associated with this input.
   *  We only need this so we can free it on exit.
   *  This is set by <code>setLexer</code>.
   *  NOTE: We assume that we <em>can</em> free it on exit. No sharing! */
  pBOUNDED_TOKEN_BUFFER d_tokenBuffer;

  /** Turns an ANTLR3 exception into a message for the user and calls <code>parseError</code>. */
  static void reportError(pANTLR3_BASE_RECOGNIZER recognizer);

  /** Builds a message for a lexer error and calls <code>parseError</code>. */
  static void lexerError(pANTLR3_BASE_RECOGNIZER recognizer);

  /** Returns the next available lexer token from the current input stream. */
  /* - auxillary function */
  static pANTLR3_COMMON_TOKEN
  nextTokenStr (pANTLR3_TOKEN_SOURCE toksource);
  /* - main function */
  static pANTLR3_COMMON_TOKEN
  nextToken (pANTLR3_TOKEN_SOURCE toksource);

  /* Since we own d_tokenStream and it needs to be freed, we need to prevent
   * copy construction and assignment.
   */
  AntlrInput(const AntlrInput& input);
  AntlrInput& operator=(const AntlrInput& input);

public:

  /** Destructor. Frees the token stream and closes the input. */
  virtual ~AntlrInput();

  /** Create an input for the given AntlrInputStream.
   * NOTE: the new Input will take ownership of the input stream and delete it
   * at destruction time.
   *
   * @param lang the input language
   * @param inputStream the input stream
   *
   * */
  static AntlrInput* newInput(InputLanguage lang, AntlrInputStream& inputStream);

  /** Retrieve the text associated with a token. */
  static std::string tokenText(pANTLR3_COMMON_TOKEN token);

  /** Retrieve a substring of the text associated with a token.
   *
   * @param token the token
   * @param index the index of the starting character of the substring
   * @param n the size of the substring. If <code>n</code> is 0, then all of the
   * characters up to the end of the token text will be included. If <code>n</code>
   * would make the substring span past the end of the token text, only those
   * characters up to the end of the token text will be included.
   */
  static std::string tokenTextSubstr(pANTLR3_COMMON_TOKEN token, size_t index, size_t n = 0);

  /** Retrieve an unsigned from the text of a token */
  static unsigned tokenToUnsigned( pANTLR3_COMMON_TOKEN token );

  /** Retrieve an Integer from the text of a token */
  static Rational tokenToInteger( pANTLR3_COMMON_TOKEN token );

  /** Retrieve a Rational from the text of a token */
  static Rational tokenToRational(pANTLR3_COMMON_TOKEN token);

  /** Get a bitvector constant from the text of the number and the size token */
  static BitVector tokenToBitvector(pANTLR3_COMMON_TOKEN number, pANTLR3_COMMON_TOKEN size);

  /** Get the ANTLR3 lexer for this input. */
  pANTLR3_LEXER getAntlr3Lexer() { return d_lexer; }

  pANTLR3_INPUT_STREAM getAntlr3InputStream() { return d_antlr3InputStream; }
protected:
  /** Create an input. This input takes ownership of the given input stream,
   * and will delete it at destruction time.
   *
   * @param inputStream the input stream to use
   * @param lookahead the lookahead needed to parse the input (i.e., k for
   * an LL(k) grammar)
   */
  AntlrInput(AntlrInputStream& inputStream, unsigned int lookahead);

  /** Retrieve the token stream for this parser. Must not be called before
   * <code>setLexer()</code>. */
  pANTLR3_COMMON_TOKEN_STREAM getTokenStream();

  /**
   * Issue a non-fatal warning to the user with file, line, and column info.
   */
  void warning(const std::string& msg) override;

  /**
   * Throws a <code>ParserException</code> with the given message.
   */
  void parseError(const std::string& msg, bool eofException = false) override;

  /** Set the ANTLR3 lexer for this input. */
  void setAntlr3Lexer(pANTLR3_LEXER pLexer);

  /** Set the ANTLR3 parser implementation for this input. */
  void setAntlr3Parser(pANTLR3_PARSER pParser);

  /** Set the Parser object for this input. */
  void setParser(Parser& parser) override;
};/* class AntlrInput */

inline std::string AntlrInput::tokenText(pANTLR3_COMMON_TOKEN token) {
  if( token->type == ANTLR3_TOKEN_EOF ) {
    return "<<EOF>>";
  }

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

inline std::string AntlrInput::tokenTextSubstr(pANTLR3_COMMON_TOKEN token,
                                               size_t index,
                                               size_t n) {

  ANTLR3_MARKER start = token->getStartIndex(token);
  // Its the last character of the token (not the one just after)
  ANTLR3_MARKER end = token->getStopIndex(token);
  assert( start < end );
  if( index > (size_t) end - start ) {
    std::stringstream ss;
    ss << "Out-of-bounds substring index: " << index;
    throw std::invalid_argument(ss.str());
  }
  start += index;
  if( n==0 || n > (size_t) end - start ) {
    return std::string( (const char *)start, end-start+1 );
  } else {
    return std::string( (const char *)start, n );
  }
}

inline unsigned AntlrInput::tokenToUnsigned(pANTLR3_COMMON_TOKEN token) {
  unsigned result;
  std::stringstream ss;
  ss << tokenText(token);
  ss >> result;
  return result;
}

inline Rational AntlrInput::tokenToInteger(pANTLR3_COMMON_TOKEN token) {
  return Rational( tokenText(token) );
}

inline Rational AntlrInput::tokenToRational(pANTLR3_COMMON_TOKEN token) {
  return Rational::fromDecimal( tokenText(token) );
}

inline BitVector AntlrInput::tokenToBitvector(pANTLR3_COMMON_TOKEN number, pANTLR3_COMMON_TOKEN size) {
  std::string number_str = tokenTextSubstr(number, 2);
  unsigned sz = tokenToUnsigned(size);
  Integer val(number_str);
  if(val.modByPow2(sz) != val) {
    std::stringstream ss;
    ss << "Overflow in bitvector construction (specified bitvector size " << sz << " too small to hold value " << tokenText(number) << ")";
    throw std::invalid_argument(ss.str());
  }
  return BitVector(sz, val);
}

}/* CVC4::parser namespace */
}/* CVC4 namespace */

#endif /* CVC4__PARSER__ANTLR_INPUT_H */

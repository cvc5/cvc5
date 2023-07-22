/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base class lexer
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__LEXER_H
#define CVC5__PARSER__LEXER_H

#include <fstream>
#include <iosfwd>
#include <string>
#include <vector>

#include "base/check.h"
#include "parser/input.h"
#include "parser/tokens.h"

namespace cvc5 {
namespace parser {

/** A location for tracking parse errors */
struct Location
{
  Location() : d_line(1), d_column(1) {}
  uint32_t d_line;
  uint32_t d_column;
};
std::ostream& operator<<(std::ostream& o, const Location& l);

/** A span for tracking parse errors */
struct Span
{
  Location d_start;
  Location d_end;
};
std::ostream& operator<<(std::ostream& o, const Span& l);

#define INPUT_BUFFER_SIZE 32768

/**
 * The base lexer class. The main methods to override are initialize and
 * nextTokenInternal.
 */
class Lexer
{
 public:
  Lexer();
  virtual ~Lexer() {}
  /**
   * Initialize the lexer to generate tokens from stream input.
   * @param input The input stream
   * @param inputName The name for debugging
   */
  virtual void initialize(Input* input, const std::string& inputName);
  /**
   * String corresponding to the last token (old top of stack). This is only
   * valid if no tokens are currently peeked.
   */
  virtual const char* tokenStr() const = 0;
  /** Advance to the next token (pop from stack) */
  Token nextToken();
  /** Add a token back into the stream (push to stack) */
  Token peekToken();
  /** Expect a token `t` as the next one. Error o.w. */
  void eatToken(Token t);
  /**
   * Expect a token `t` or `f` as the next one, or throw a parse error
   * otherwise. Return true if `t`.
   */
  bool eatTokenChoice(Token t, Token f);
  /** reinsert token, read back first in, last out */
  void reinsertToken(Token t);
  /** Used to report warnings, with the current source location attached. */
  void warning(const std::string&);
  /** Used to report errors, with the current source location attached. */
  void parseError(const std::string&, bool eofException = false);
  /** Error. Got `t`, expected `info`. */
  void unexpectedTokenError(Token t, const std::string& info);

 protected:
  // -----------------
  /** Compute the next token by reading from the stream */
  virtual Token nextTokenInternal() = 0;
  /** Get the next character */
  char readNextChar()
  {
    if (d_bufferPos < d_bufferEnd)
    {
      d_ch = d_buffer[d_bufferPos];
      d_bufferPos++;
    }
    else if (d_isInteractive)
    {
      d_ch = d_istream->get();
    }
    else
    {
      d_istream->read(d_buffer, INPUT_BUFFER_SIZE);
      d_bufferEnd = static_cast<size_t>(d_istream->gcount());
      if (d_bufferEnd == 0)
      {
        d_ch = EOF;
        d_bufferPos = 0;
      }
      else
      {
        d_ch = d_buffer[0];
        d_bufferPos = 1;
      }
    }
    return d_ch;
  }
  /** Get the next character */
  char nextChar()
  {
    char res;
    if (d_peekedChar)
    {
      res = d_chPeeked;
      d_peekedChar = false;
    }
    else
    {
      res = readNextChar();
      if (res == '\n')
      {
        d_span.d_end.d_line++;
        d_span.d_end.d_column = 0;
      }
      else
      {
        d_span.d_end.d_column++;
      }
    }
    return res;
  }
  /** Save character */
  void saveChar(char ch)
  {
    Assert(!d_peekedChar);
    d_peekedChar = true;
    d_chPeeked = ch;
  }
  // -----------------
  /** Used to initialize d_span. */
  void initSpan();
  /** Sets the spans start to its current end. */
  void bumpSpan()
  {
    d_span.d_start.d_line = d_span.d_end.d_line;
    d_span.d_start.d_column = d_span.d_end.d_column;
  }
  /** Add columns or lines to the end location of the span. */
  void addColumns(uint32_t columns) { d_span.d_end.d_column += columns; }
  void addLines(uint32_t lines)
  {
    d_span.d_end.d_line += lines;
    d_span.d_end.d_column = 0;
  }
  /** Span of last token pulled from underlying lexer (old top of stack) */
  Span d_span;
  /** Name of current input, for debugging */
  std::string d_inputName;
  /**
   * The peeked stack. When we peek at the next token, it is added to this
   * vector. When we read a token, if this vector is non-empty, we return the
   * back of it and pop.
   */
  std::vector<Token> d_peeked;

 private:
  /** The input */
  std::istream* d_istream;
  /** True if the input stream is interactive */
  bool d_isInteractive;
  /** The current buffer */
  char d_buffer[INPUT_BUFFER_SIZE];
  /** The position in the current buffer we are reading from */
  size_t d_bufferPos;
  /** The size of characters in the current buffer */
  size_t d_bufferEnd;
  /** The current character we read. */
  char d_ch;
  /** True if we have a saved character that has not been consumed yet. */
  bool d_peekedChar;
  /** The saved character. */
  char d_chPeeked;
};

}  // namespace parser
}  // namespace cvc5

#endif

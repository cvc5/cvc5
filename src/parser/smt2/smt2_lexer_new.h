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
 * The lexer for smt2
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__SMT2__SMT2_LEXER_NEW_H
#define CVC5__PARSER__SMT2__SMT2_LEXER_NEW_H

#include <cstdlib>
#include <istream>
#include <map>
#include <vector>

#include "parser/flex_lexer.h"
#include "parser/tokens.h"

namespace cvc5 {
namespace parser {

/**
 * The lexer for Smt2. This handles lexing tokens that may appear in smt2
 * terms. It does not lex command tokens.
 *
 * Partially based on
 * https://github.com/bitwuzla/bitwuzla/blob/dev/src/parser/smt2/lexer.h
 */
class Smt2LexerNew : public FlexLexer
{
 public:
  Smt2LexerNew(bool isStrict, bool isSygus);
  const char* tokenStr() const override;
  /** Are we in strict mode? */
  bool isStrict() const;
  /** Are we parsing sygus? */
  bool isSygus() const;

 private:
  /**
   * Read and tokenize the next token from the provided input stream. Stores
   * its characters to d_token.
   */
  Token nextTokenInternal() override;
  /**
   * Computes the next token and adds its characters to d_token. Does not
   * null terminate.
   */
  Token computeNextToken();
  /** Get the next character */
  char nextChar();
  /** Save character */
  void saveChar(char ch);
  /** Push a character to the stored token */
  void pushToToken(char ch);
  //----------- Utilities for parsing the current character stream
  enum class CharacterClass
  {
    NONE,
    WHITESPACE,
    DECIMAL_DIGIT,
    HEXADECIMAL_DIGIT,
    BIT,
    SYMBOL_START,
    SYMBOL,
  };
  /** parse <c>, return false if <c> is not ch. */
  bool parseLiteralChar(char ch);
  /** parse <c>, return false if <c> is not from cc */
  bool parseChar(CharacterClass cc);
  /** parse <c>+ from cc, return false if the next char is not from cc. */
  bool parseNonEmptyCharList(CharacterClass cc);
  /** parse <c>* from cc. */
  void parseCharList(CharacterClass cc);
  /** Return true if ch is in character class cc */
  bool isCharacterClass(char ch, CharacterClass cc) const{
  switch (cc)
  {
    case CharacterClass::WHITESPACE:
      return d_symcTable[static_cast<size_t>(ch)]==CharacterClass::WHITESPACE;
    case CharacterClass::DECIMAL_DIGIT:
      return d_symcTable[static_cast<size_t>(ch)]==CharacterClass::DECIMAL_DIGIT;
    case CharacterClass::HEXADECIMAL_DIGIT:
      return (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f')
             || (ch >= 'A' && ch <= 'F');
    case CharacterClass::BIT: return ch == '0' || ch == '1';
    case CharacterClass::SYMBOL_START:
      return d_symcTable[static_cast<size_t>(ch)]==CharacterClass::SYMBOL;
    case CharacterClass::SYMBOL:
    {
      CharacterClass chcc = d_symcTable[static_cast<size_t>(ch)];
      return chcc==CharacterClass::SYMBOL || chcc == CharacterClass::DECIMAL_DIGIT;
    }
    default: break;
  }
  return false;
}
  //----------- Utilizes for tokenizing d_token
  /**
   * Tokenize current symbol stored in d_token.
   *
   * This method changes the string in d_token into the appropriate token.
   * Otherwise, we return Token::SYMBOL.
   *
   * The list of all simple symbols that are converted by this method.
   *   as, par, let, match, Constant, Variable, _
   *
   * We don't handle command tokens here.
   */
  Token tokenizeCurrentSymbol() const;
  /** The characters in the current token */
  std::vector<char> d_token;
  /** True if we have a saved character that has not been consumed yet. */
  bool d_peekedChar;
  /** The saved character. */
  char d_chPeeked;
  /** Is strict parsing enabled */
  bool d_isStrict;
  /** Is sygus enabled */
  bool d_isSygus;
  /**
   * Static table denoting a representative character class for characters
   * 0...255, used for computing isCharacterClass.
   */
  CharacterClass d_symcTable[256];
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2__SMT2_LEXER_NEW_H */

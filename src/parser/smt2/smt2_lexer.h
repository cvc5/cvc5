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

#ifndef CVC5__PARSER__SMT2__SMT2_LEXER_H
#define CVC5__PARSER__SMT2__SMT2_LEXER_H

#include <array>
#include <cstdlib>
#include <istream>
#include <map>
#include <vector>

#include "base/check.h"
#include "parser/lexer.h"
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
class Smt2Lexer : public Lexer
{
 public:
  Smt2Lexer(bool isStrict, bool isSygus);
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
  /** Push a character to the stored token */
  void pushToToken(char ch)
  {
    Assert(ch != EOF);
    d_token.push_back(ch);
  }
  //----------- Utilities for parsing the current character stream
  enum class CharacterClass
  {
    NONE = 0,
    WHITESPACE = (1 << 0),
    DECIMAL_DIGIT = (1 << 1),
    HEXADECIMAL_DIGIT = (1 << 2),
    BIT = (1 << 3),
    SYMBOL_START = (1 << 4),
    SYMBOL = (1 << 5),
  };
  /** The set of non-letter/non-digit characters that may occur in keywords. */
  inline static const std::string s_extraSymbolChars = "+-/*=%?!.$_~&^<>@";
  /** parse <c>, return false if <c> is not ch. */
  bool parseLiteralChar(char ch);
  /** parse <c>, return false if <c> is not from cc */
  bool parseChar(CharacterClass cc);
  /** parse <c>+ from cc, return false if the next char is not from cc. */
  bool parseNonEmptyCharList(CharacterClass cc);
  /** parse <c>* from cc. */
  void parseCharList(CharacterClass cc);
  /** Return true if ch is in character class cc */
  bool isCharacterClass(char ch, CharacterClass cc) const
  {
    return d_charClass[static_cast<uint8_t>(ch)] & static_cast<uint8_t>(cc);
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
  /** Is strict parsing enabled */
  bool d_isStrict;
  /** Is sygus enabled */
  bool d_isSygus;
  /** The character classes. */
  std::array<uint8_t, 256> d_charClass{};  // value-initialized to 0
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2__SMT2_LEXER_NEW_H */

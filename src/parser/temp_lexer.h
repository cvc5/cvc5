/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Temp
 */

#include "cvc5parser_private.h"

#ifndef CVC5__PARSER__TEMP_LEXER_H
#define CVC5__PARSER__TEMP_LEXER_H

#include <cstdlib>
#include <istream>
#include <vector>

#include "parser/tokens.h"

namespace cvc5 {
namespace parser {

class FlexLexer;

class TempLexer
{
 public:
  TempLexer(FlexLexer& p);
  void initialize(std::istream* input);
  const char* tokenStr();
  Token nextToken();

 private:
  enum class CharacterClass
  {
    DECIMAL_DIGIT,
    HEXADECIMAL_DIGIT,
    BIT,
    SYMBOL_START,
    SYMBOL,
  };
  /** Get the next character */
  int32_t nextChar();
  /** Save character */  
  void saveChar(int32_t ch);
  void pushToToken(int32_t ch);
  //-----------
  /** parse <c> */
  bool parseLiteralChar(int32_t ch);
  /** parse <c> */
  bool parseChar(CharacterClass cc);
  /** parse <c>+ */
  bool parseNonEmptyCharList(CharacterClass cc);
  /** parse <c>* */
  void parseCharList(CharacterClass cc);
  /** is character class */
  static bool isCharacterClass(int32_t ch, CharacterClass cc);
  //-----------
  FlexLexer& d_parent;
  std::istream* d_input;
  std::vector<char> d_token;
  /** True if we have a saved character that has not been consumed yet. */
  bool d_peeked;
  /** The saved character. */
  int32_t d_peekedChar;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__TEMP_LEXER_H */

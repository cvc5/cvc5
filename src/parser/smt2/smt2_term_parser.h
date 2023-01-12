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
 * Term parser for smt2
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2__SMT2_TERM_PARSER_H
#define CVC5__PARSER__SMT2__SMT2_TERM_PARSER_H

#include "api/cpp/cvc5.h"
#include "parser/smt2/smt2.h"
#include "parser/smt2/smt2_lexer.h"

namespace cvc5 {
namespace parser {

/**
 * The smt2 term parser, which parses terms, sorts, symbol expressions
 * and other miscellaneous expressions from the SMT2 language. It reads
 * from the given lexer.
 */
class Smt2TermParser
{
 public:
  Smt2TermParser(Smt2Lexer& lex, Smt2State& state);
  virtual ~Smt2TermParser() {}

  /** Parse symbol */
  std::string parseSymbol(DeclarationCheck check = CHECK_NONE,
                          SymbolType type = SYM_SORT);
  /** Parse parentheses-enclosed sorted variable list */
  std::vector<std::string> parseSymbolList(DeclarationCheck check = CHECK_NONE,
                                           SymbolType type = SYM_SORT);
  /**
   * Parses ':X', returns 'X'
   */
  std::string parseKeyword();
  /** Parse integer numeral */
  uint32_t parseIntegerNumeral();
  /**
   * Parse numeral list without parentheses
   */
  std::vector<std::string> parseNumeralList();
  /**
   * Matches a string, and (optionally) strips off the quotes/unescapes the
   * string when `unescape` is set to true.
   */
  std::string parseStr(bool unescape);

 protected:
  /** Return the unsigned for the current token string. */
  uint32_t tokenStrToUnsigned();
  /**
   * Return the string content of the current token string when interpreted
   * as the given token, e.g. return`abc` for token string `|abc|` where
   * tok is QUOTED_SYMBOL.
   */
  std::string tokenStrToSymbol(Token tok);
  /**
   * Unescape string, which updates s based on processing escape sequences
   * as defined in SMT2.
   */
  void unescapeString(std::string& s);
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The state */
  Smt2State& d_state;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_TERM_PARSER_H */

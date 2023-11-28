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
 * Term parser for smt2
 */

#include "cvc5parser_public.h"

#ifndef CVC5__PARSER__SMT2__SMT2_TERM_PARSER_H
#define CVC5__PARSER__SMT2__SMT2_TERM_PARSER_H

#include <cvc5/cvc5.h>

#include "parser/smt2/smt2_state.h"
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

  /** Parses an SMT-LIB term <term> */
  Term parseTerm();
  /** Parses parentheses-enclosed term list (<term>*) */
  std::vector<Term> parseTermList();
  /** Parse an SMT-LIB sort <sort> */
  Sort parseSort();
  /** Parses parentheses-enclosed sort list (<sort>*) */
  std::vector<Sort> parseSortList();
  /**
   * Parse parentheses-enclosed sorted variable list of the form:
   * ((<symbol> <sort>)*)
   */
  std::vector<std::pair<std::string, Sort>> parseSortedVarList();
  /**
   * Parses an SMT-LIB symbolic expr. A symbolic expression has the syntax:
   * <sexpr> := (<sexpr>*) | <symbol> | <spec_constant>
   * The returned term has AST that consists of applications of SEXPR (for the
   * first case of the BNF) and constant strings (for the latter two cases).
   */
  Term parseSymbolicExpr();
  /**
   * Parse symbol, which returns the string of the parsed symbol if the next
   * token is a valid smt2 symbol.
   *
   * @param check Specifies whether to check if the symbol is already declared
   * or not declared,
   * @param type The type of symbol we are expecting (variable or sort).
   */
  std::string parseSymbol(DeclarationCheck check = CHECK_NONE,
                          SymbolType type = SYM_VARIABLE);
  /**
   * Parse parentheses-enclosed symbol list.
   * Expects to parse '(<symbol>*)', where '<symbol>' is parsed by the above
   * method.
   */
  std::vector<std::string> parseSymbolList(DeclarationCheck check = CHECK_NONE,
                                           SymbolType type = SYM_VARIABLE);
  /**
   * Parses ':X', returns 'X'
   */
  std::string parseKeyword();
  /**
   * Parse grammar, SyGuS 2.1 <GrammarDef>, which has syntax:
   *
   * <GrammarDef> := ((<symbol> <sort>)^n+1) (<GroupedRuleList>^n+1)
   * <GroupedRuleList> := (<symbol> <Sort> (<GTerm>+))
   * where <GTerm> is a term that additionally allows the SyGuS-specific
   * grammar rules for Constant and Variable.
   */
  Grammar* parseGrammar(const std::vector<Term>& sygusVars,
                        const std::string& fun);
  /**
   * Parse optional grammar <GrammarDef>?, return null if a grammar was not
   * parsed.
   */
  Grammar* parseGrammarOrNull(const std::vector<Term>& sygusVars,
                              const std::string& fun);
  /** Parse integer numeral */
  uint32_t parseIntegerNumeral();
  /**
   * Parse numeral list without parentheses
   */
  std::vector<std::string> parseNumeralList();
  /**
   * Parse datatype def '<datatype_dec>', not parentheses enclosed. The syntax
   * for datatype declarations is:
   *
   * datatype_dec :=
   *   (<constructor_dec>+) | (par (<symbol>+) (<constructor_dec>+))
   * constructor_dec := (<symbol> (<symbol> <sort>)∗)
   */
  std::vector<DatatypeDecl> parseDatatypesDef(
      bool isCo,
      const std::vector<std::string>& dnames,
      const std::vector<size_t>& arities);
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
  /**
   * Parse constructor definition list, add to declaration type. The expected
   * syntax is '(<constructor_dec>+)'.
   */
  void parseConstructorDefinitionList(DatatypeDecl& type);
  /**
   * Continue parse indexed identifier, we've parsed '(_ ', now parse
   * remainder '<symbol> <index>+)' and return the result.
   */
  ParseOp continueParseIndexedIdentifier(bool isOperator);
  /**
   * Continue parse qualified identifier, we've parsed '(as ', now parse
   * remainder '<identifier> <type>)' and return the result.
   */
  ParseOp continueParseQualifiedIdentifier(bool isOperator);
  /**
   * Parse match case pattern
   */
  Term parseMatchCasePattern(Sort headSort, std::vector<Term>& boundVars);
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The state */
  Smt2State& d_state;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_TERM_PARSER_H */

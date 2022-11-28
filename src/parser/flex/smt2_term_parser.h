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

#ifndef CVC5__PARSER__SMT2_TERM_PARSER_H
#define CVC5__PARSER__SMT2_TERM_PARSER_H

#include "api/cpp/cvc5.h"
#include "parser/flex/smt2_lexer.h"
#include "parser/smt2/smt2_state.h"

namespace cvc5 {
namespace parser {

/**
 */
class Smt2TermParser
{
 public:
  Smt2TermParser(Smt2Lexer& lex, Smt2State& state);
  virtual ~Smt2TermParser() {}

  /** Parses a term */
  Term parseTerm();
  /** Parses parentheses-enclosed term list */
  std::vector<Term> parseTermList();
  /** Parses a symbolic expr */
  Term parseSymbolicExpr();
  /** Parse a sort */
  Sort parseSort();
  /** Parses parentheses-enclosed sort list */
  std::vector<Sort> parseSortList();
  /** Parse parentheses-enclosed sorted variable list */
  std::vector<std::pair<std::string, Sort> > parseSortedVarList();
  /** Parse symbol */
  const std::string& parseSymbol(DeclarationCheck check = CHECK_NONE,
                                 SymbolType type = SYM_SORT);
  /**
   * Parses ':X', returns 'X'
   */
  const std::string& parseKeyword();
  /** Parse grammar */
  Grammar* parseGrammar(const std::vector<Term>& sygusVars,
                        const std::string& fun);
  /** Parse integer numeral */
  size_t parseIntegerNumeral();
  /** Parse datatype def */
  std::vector<DatatypeDecl> parseDatatypeDef(
      bool isCo,
      const std::vector<std::string>& dnames,
      const std::vector<size_t>& arities);

 protected:
  /** The lexer */
  Smt2Lexer& d_lex;
  /** The state */
  Smt2State& d_state;
};

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__SMT2_TERM_PARSER_H */

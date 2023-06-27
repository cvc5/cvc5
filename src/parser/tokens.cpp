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
 * Definitions of SMT2 tokens.
 */

#include "parser/tokens.h"

#include <iostream>

namespace cvc5 {
namespace parser {

std::ostream& operator<<(std::ostream& o, Token t)
{
  switch (t)
  {
    case Token::EOF_TOK: o << "EOF_TOK"; break;
    case Token::ALPHA: o << "ALPHA"; break;
    case Token::ASSERT_TOK: o << "ASSERT_TOK"; break;
    case Token::ASSUME_TOK: o << "ASSUME_TOK"; break;
    case Token::AS_TOK: o << "AS_TOK"; break;
    case Token::ATTRIBUTE_TOK: o << "ATTRIBUTE_TOK"; break;
    case Token::BINARY_LITERAL: o << "BINARY_LITERAL"; break;
    case Token::BLOCK_MODEL_TOK: o << "BLOCK_MODEL_TOK"; break;
    case Token::BLOCK_MODEL_VALUES_TOK: o << "BLOCK_MODEL_VALUES_TOK"; break;
    case Token::CHECK_SAT_ASSUMING_TOK: o << "CHECK_SAT_ASSUMING_TOK"; break;
    case Token::CHECK_SAT_TOK: o << "CHECK_SAT_TOK"; break;
    case Token::CHECK_SYNTH_NEXT_TOK: o << "CHECK_SYNTH_NEXT_TOK"; break;
    case Token::CHECK_SYNTH_TOK: o << "CHECK_SYNTH_TOK"; break;
    case Token::CONSTRAINT_TOK: o << "CONSTRAINT_TOK"; break;
    case Token::DECIMAL_LITERAL: o << "DECIMAL_LITERAL"; break;
    case Token::DECLARE_CODATATYPES_TOK: o << "DECLARE_CODATATYPES_TOK"; break;
    case Token::DECLARE_CODATATYPE_TOK: o << "DECLARE_CODATATYPE_TOK"; break;
    case Token::DECLARE_CONST_TOK: o << "DECLARE_CONST_TOK"; break;
    case Token::DECLARE_DATATYPES_TOK: o << "DECLARE_DATATYPES_TOK"; break;
    case Token::DECLARE_DATATYPE_TOK: o << "DECLARE_DATATYPE_TOK"; break;
    case Token::DECLARE_FUN_TOK: o << "DECLARE_FUN_TOK"; break;
    case Token::DECLARE_HEAP_TOK: o << "DECLARE_HEAP_TOK"; break;
    case Token::DECLARE_ORACLE_FUN_TOK: o << "DECLARE_ORACLE_FUN_TOK"; break;
    case Token::DECLARE_POOL_TOK: o << "DECLARE_POOL_TOK"; break;
    case Token::DECLARE_SORT_TOK: o << "DECLARE_SORT_TOK"; break;
    case Token::DECLARE_VAR_TOK: o << "DECLARE_VAR_TOK"; break;
    case Token::DEFINE_CONST_TOK: o << "DEFINE_CONST_TOK"; break;
    case Token::DEFINE_FUNS_REC_TOK: o << "DEFINE_FUNS_REC_TOK"; break;
    case Token::DEFINE_FUN_REC_TOK: o << "DEFINE_FUN_REC_TOK"; break;
    case Token::DEFINE_FUN_TOK: o << "DEFINE_FUN_TOK"; break;
    case Token::DEFINE_SORT_TOK: o << "DEFINE_SORT_TOK"; break;
    case Token::ECHO_TOK: o << "ECHO_TOK"; break;
    case Token::EXIT_TOK: o << "EXIT_TOK"; break;
    case Token::FIELD_LITERAL: o << "FIELD_LITERAL"; break;
    case Token::GET_ABDUCT_NEXT_TOK: o << "GET_ABDUCT_NEXT_TOK"; break;
    case Token::GET_ABDUCT_TOK: o << "GET_ABDUCT_TOK"; break;
    case Token::GET_ASSERTIONS_TOK: o << "GET_ASSERTIONS_TOK"; break;
    case Token::GET_ASSIGNMENT_TOK: o << "GET_ASSIGNMENT_TOK"; break;
    case Token::GET_DIFFICULTY_TOK: o << "GET_DIFFICULTY_TOK"; break;
    case Token::GET_INFO_TOK: o << "GET_INFO_TOK"; break;
    case Token::GET_INTERPOL_NEXT_TOK: o << "GET_INTERPOL_NEXT_TOK"; break;
    case Token::GET_INTERPOL_TOK: o << "GET_INTERPOL_TOK"; break;
    case Token::GET_LEARNED_LITERALS_TOK:
      o << "GET_LEARNED_LITERALS_TOK";
      break;
    case Token::GET_MODEL_TOK: o << "GET_MODEL_TOK"; break;
    case Token::GET_OPTION_TOK: o << "GET_OPTION_TOK"; break;
    case Token::GET_PROOF_TOK: o << "GET_PROOF_TOK"; break;
    case Token::GET_QE_DISJUNCT_TOK: o << "GET_QE_DISJUNCT_TOK"; break;
    case Token::GET_QE_TOK: o << "GET_QE_TOK"; break;
    case Token::GET_TIMEOUT_CORE_TOK: o << "GET_TIMEOUT_CORE_TOK"; break;
    case Token::GET_UNSAT_ASSUMPTIONS_TOK:
      o << "GET_UNSAT_ASSUMPTIONS_TOK";
      break;
    case Token::GET_UNSAT_CORE_TOK: o << "GET_UNSAT_CORE_TOK"; break;
    case Token::GET_VALUE_TOK: o << "GET_VALUE_TOK"; break;
    case Token::HEX_LITERAL: o << "HEX_LITERAL"; break;
    case Token::INCLUDE_TOK: o << "INCLUDE_TOK"; break;
    case Token::INDEX_TOK: o << "INDEX_TOK"; break;
    case Token::INTEGER_LITERAL: o << "INTEGER_LITERAL"; break;
    case Token::INV_CONSTRAINT_TOK: o << "INV_CONSTRAINT_TOK"; break;
    case Token::KEYWORD: o << "KEYWORD"; break;
    case Token::LET_TOK: o << "LET_TOK"; break;
    case Token::LPAREN_TOK: o << "LPAREN_TOK"; break;
    case Token::MATCH_TOK: o << "MATCH_TOK"; break;
    case Token::NUMERAL: o << "NUMERAL"; break;
    case Token::PAR_TOK: o << "PAR_TOK"; break;
    case Token::POP_TOK: o << "POP_TOK"; break;
    case Token::PUSH_TOK: o << "PUSH_TOK"; break;
    case Token::QUOTED_SYMBOL: o << "QUOTED_SYMBOL"; break;
    case Token::RESET_ASSERTIONS_TOK: o << "RESET_ASSERTIONS_TOK"; break;
    case Token::RESET_TOK: o << "RESET_TOK"; break;
    case Token::RPAREN_TOK: o << "RPAREN_TOK"; break;
    case Token::SET_FEATURE_TOK: o << "SET_FEATURE_TOK"; break;
    case Token::SET_INFO_TOK: o << "SET_INFO_TOK"; break;
    case Token::SET_LOGIC_TOK: o << "SET_LOGIC_TOK"; break;
    case Token::SET_OPTION_TOK: o << "SET_OPTION_TOK"; break;
    case Token::SIMPLIFY_TOK: o << "SIMPLIFY_TOK"; break;
    case Token::STRING_LITERAL: o << "STRING_LITERAL"; break;
    case Token::SYMBOL: o << "SYMBOL"; break;
    case Token::SYNTH_FUN_TOK: o << "SYNTH_FUN_TOK"; break;
    case Token::SYNTH_INV_TOK: o << "SYNTH_INV_TOK"; break;
    case Token::UNTERMINATED_QUOTED_SYMBOL:
      o << "UNTERMINATED_QUOTED_SYMBOL";
      break;
    case Token::UNTERMINATED_STRING_LITERAL:
      o << "UNTERMINATED_STRING_LITERAL";
      break;
    case Token::NONE: o << "NONE"; break;
    default: o << "Unknown Token (" << unsigned(t) << ")"; break;
  }
  return o;
}

}  // namespace parser
}  // namespace cvc5

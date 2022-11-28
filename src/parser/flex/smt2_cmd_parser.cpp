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
 * Definitions of SMT2 tokens.
 */

#include "parser/flex/smt2_cmd_parser.h"

#include "parser/api/cpp/command.h"

namespace cvc5 {
namespace parser {

Smt2CmdParser::Smt2CmdParser(Smt2Lexer& lex,
                             Smt2State& state,
                             Smt2TermParser& tparser)
    : d_lex(lex), d_state(state), d_tparser(tparser)
{
}

Command* Smt2CmdParser::parseNextCommand()
{
  std::unique_ptr<Command> cmd;
  d_lex.eatToken(Token::LPAREN_TOK);
  Token tok = d_lex.nextToken();
  switch (tok)
  {
    case Token::ASSERT_TOK:
    {
      Term t = d_tparser.parseTerm();
    }
      break;
    case Token::ASSUME_TOK: break;
    case Token::BLOCK_MODEL_TOK: break;
    case Token::BLOCK_MODEL_VALUES_TOK: break;
    case Token::CHECK_SAT_TOK: break;
    case Token::CHECK_SAT_ASSUMING_TOK: break;
    case Token::CHECK_SYNTH_TOK: break;
    case Token::CHECK_SYNTH_NEXT_TOK: break;
    case Token::CONSTRAINT_TOK: break;
    case Token::DECLARE_CODATATYPE_TOK: break;
    case Token::DECLARE_CODATATYPES_TOK: break;
    case Token::DECLARE_CONST_TOK: break;
    case Token::DECLARE_DATATYPE_TOK: break;
    case Token::DECLARE_DATATYPES_TOK: break;
    case Token::DECLARE_FUN_TOK: break;
    case Token::DECLARE_HEAP: break;
    case Token::DECLARE_POOL: break;
    case Token::DECLARE_SORT_TOK: break;
    case Token::DECLARE_VAR_TOK: break;
    case Token::DEFINE_CONST_TOK: break;
    case Token::DEFINE_FUN_TOK: break;
    case Token::DEFINE_FUN_REC_TOK: break;
    case Token::DEFINE_FUNS_REC_TOK: break;
    case Token::DEFINE_SORT_TOK: break;
    case Token::ECHO_TOK: break;
    case Token::EXIT_TOK: break;
    case Token::GET_ABDUCT_TOK: break;
    case Token::GET_ABDUCT_NEXT_TOK: break;
    case Token::GET_ASSERTIONS_TOK: break;
    case Token::GET_ASSIGNMENT_TOK: break;
    case Token::GET_DIFFICULTY_TOK: break;
    case Token::GET_INFO_TOK: break;
    case Token::GET_INTERPOL_TOK: break;
    case Token::GET_INTERPOL_NEXT_TOK: break;
    case Token::GET_LEARNED_LITERALS_TOK: break;
    case Token::GET_MODEL_TOK: break;
    case Token::GET_OPTION_TOK: break;
    case Token::GET_PROOF_TOK: break;
    case Token::GET_QE_TOK: break;
    case Token::GET_QE_DISJUNCT_TOK: break;
    case Token::GET_UNSAT_ASSUMPTIONS_TOK: break;
    case Token::GET_UNSAT_CORE_TOK: break;
    case Token::GET_VALUE_TOK: break;
    case Token::INV_CONSTRAINT_TOK: break;
    case Token::POP_TOK: break;
    case Token::PUSH_TOK: break;
    case Token::RESET_TOK: break;
    case Token::RESET_ASSERTIONS_TOK: break;
    case Token::SET_FEATURE_TOK: break;
    case Token::SET_INFO_TOK: break;
    case Token::SET_LOGIC_TOK: 
    {
      const std::string& name = d_tparser.parseSymbol();
      cmd.reset(d_state.setLogic(name));
    }
    break;
    case Token::SET_OPTION_TOK: break;
    case Token::SIMPLIFY_TOK: break;
    case Token::SYNTH_FUN_TOK: break;
    case Token::SYNTH_INV_TOK: break;
    default:
      // TODO: error
      break;
  }
  d_lex.eatToken(Token::RPAREN_TOK);
  return cmd.release();
}

}  // namespace parser
}  // namespace cvc5

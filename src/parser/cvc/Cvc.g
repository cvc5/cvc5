/* *******************                                                        */
/*! \file Cvc.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Parser for CVC presentation input language
 **
 ** Parser for CVC presentation input language.
 **/

grammar Cvc;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in cvc_input.cpp !
  k = 3;
}/* options */

tokens {
  /* commands */

  ASSERT_TOK = 'ASSERT';
  QUERY_TOK = 'QUERY';
  CHECKSAT_TOK = 'CHECKSAT';
  OPTION_TOK = 'OPTION';
  PUSH_TOK = 'PUSH';
  POP_TOK = 'POP';
  POPTO_TOK = 'POPTO';
  PUSH_SCOPE_TOK = 'PUSH_SCOPE';
  POP_SCOPE_TOK = 'POP_SCOPE';
  POPTO_SCOPE_TOK = 'POPTO_SCOPE';
  RESET_TOK = 'RESET';
  DATATYPE_TOK = 'DATATYPE';
  END_TOK = 'END';
  CONTEXT_TOK = 'CONTEXT';
  FORGET_TOK = 'FORGET';
  GET_TYPE_TOK = 'GET_TYPE';
  CHECK_TYPE_TOK = 'CHECK_TYPE';
  GET_CHILD_TOK = 'GET_CHILD';
  GET_OP_TOK = 'GET_OP';
  GET_VALUE_TOK = 'GET_VALUE';
  SUBSTITUTE_TOK = 'SUBSTITUTE';
  DBG_TOK = 'DBG';
  TRACE_TOK = 'TRACE';
  UNTRACE_TOK = 'UNTRACE';
  HELP_TOK = 'HELP';
  TRANSFORM_TOK = 'TRANSFORM';
  PRINT_TOK = 'PRINT';
  PRINT_TYPE_TOK = 'PRINT_TYPE';
  CALL_TOK = 'CALL';
  ECHO_TOK = 'ECHO';
  EXIT_TOK = 'EXIT';
  INCLUDE_TOK = 'INCLUDE';
  DUMP_PROOF_TOK = 'DUMP_PROOF';
  DUMP_UNSAT_CORE_TOK = 'DUMP_UNSAT_CORE';
  DUMP_ASSUMPTIONS_TOK = 'DUMP_ASSUMPTIONS';
  DUMP_SIG_TOK = 'DUMP_SIG';
  DUMP_TCC_TOK = 'DUMP_TCC';
  DUMP_TCC_ASSUMPTIONS_TOK = 'DUMP_TCC_ASSUMPTIONS';
  DUMP_TCC_PROOF_TOK = 'DUMP_TCC_PROOF';
  DUMP_CLOSURE_TOK = 'DUMP_CLOSURE';
  DUMP_CLOSURE_PROOF_TOK = 'DUMP_CLOSURE_PROOF';
  WHERE_TOK = 'WHERE';
  ASSERTIONS_TOK = 'ASSERTIONS';
  ASSUMPTIONS_TOK = 'ASSUMPTIONS';
  COUNTEREXAMPLE_TOK = 'COUNTEREXAMPLE';
  COUNTERMODEL_TOK = 'COUNTERMODEL';
  ARITH_VAR_ORDER_TOK = 'ARITH_VAR_ORDER';
  CONTINUE_TOK = 'CONTINUE';
  RESTART_TOK = 'RESTART';
  RECURSIVE_FUNCTION_TOK = 'REC-FUN';
  /* operators */

  AND_TOK = 'AND';
  BOOLEAN_TOK = 'BOOLEAN';
  ELSEIF_TOK = 'ELSIF';
  ELSE_TOK = 'ELSE';
  ENDIF_TOK = 'ENDIF';
  FALSE_TOK = 'FALSE';
  IF_TOK = 'IF';
  IN_TOK = 'IN';
  INT_TOK = 'INT';
  LET_TOK = 'LET';
  MEMBER_TOK = 'IS_IN';
  NOT_TOK = 'NOT';
  OR_TOK = 'OR';
  REAL_TOK = 'REAL';
  THEN_TOK = 'THEN';
  TRUE_TOK = 'TRUE';
  TYPE_TOK = 'TYPE';
  XOR_TOK = 'XOR';

  ARRAY_TOK = 'ARRAY';
  OF_TOK = 'OF';
  WITH_TOK = 'WITH';

  SUBTYPE_TOK = 'SUBTYPE';
  SET_TOK = 'SET';

  TUPLE_TOK = 'TUPLE';

  FORALL_TOK = 'FORALL';
  EXISTS_TOK = 'EXISTS';
  PATTERN_TOK = 'PATTERN';

  LAMBDA_TOK = 'LAMBDA';

  // Symbols

  COLON = ':';
  COMMA = ',';
  LPAREN = '(';
  RPAREN = ')';
  LBRACE = '{';
  RBRACE = '}';
  LBRACKET = '[';
  RBRACKET = ']';
  SEMICOLON = ';';
  BAR = '|';
  UNDERSCORE = '_';

  SQHASH = '[#';
  HASHSQ = '#]';
  PARENHASH = '(#';
  HASHPAREN = '#)';

  // Operators

  ARROW_TOK = '->';
  DIV_TOK = '/';
  EQUAL_TOK = '=';
  DISEQUAL_TOK = '/=';
  EXP_TOK = '^';
  GT_TOK = '>';
  GEQ_TOK = '>=';
  IFF_TOK = '<=>';
  IMPLIES_TOK = '=>';
  LT_TOK = '<';
  LEQ_TOK = '<=';
  MINUS_TOK = '-';
  PLUS_TOK = '+';
  STAR_TOK = '*';
  ASSIGN_TOK = ':=';
  MOD_TOK = 'MOD';
  INTDIV_TOK = 'DIV';
  FLOOR_TOK = 'FLOOR';
  ABS_TOK = 'ABS';
  DIVISIBLE_TOK = 'DIVISIBLE';
  DISTINCT_TOK = 'DISTINCT';

  // Bitvectors

  BITVECTOR_TOK = 'BITVECTOR';
  LEFTSHIFT_TOK = '<<';
  RIGHTSHIFT_TOK = '>>';
  BVPLUS_TOK = 'BVPLUS';
  BVSUB_TOK = 'BVSUB';
  BVUDIV_TOK = 'BVUDIV';
  BVSDIV_TOK = 'BVSDIV';
  BVUREM_TOK = 'BVUREM';
  BVSREM_TOK = 'BVSREM';
  BVSMOD_TOK = 'BVSMOD';
  BVSHL_TOK = 'BVSHL';
  BVASHR_TOK = 'BVASHR';
  BVLSHR_TOK = 'BVLSHR';
  BVUMINUS_TOK = 'BVUMINUS';
  BVMULT_TOK = 'BVMULT';
  BVNEG_TOK = '~';
  BVAND_TOK = '&';
  BVXOR_TOK = 'BVXOR';
  BVNAND_TOK = 'BVNAND';
  BVNOR_TOK = 'BVNOR';
  BVCOMP_TOK = 'BVCOMP';
  BVXNOR_TOK = 'BVXNOR';
  CONCAT_TOK = '@';
  //BVTOINT_TOK = 'BVTOINT';
  //INTTOBV_TOK = 'INTTOBV';
  //BOOLEXTRACT_TOK = 'BOOLEXTRACT';
  IS_INTEGER_TOK = 'IS_INTEGER';
  BVLT_TOK = 'BVLT';
  BVGT_TOK = 'BVGT';
  BVLE_TOK = 'BVLE';
  BVGE_TOK = 'BVGE';
  SX_TOK = 'SX';
  BVZEROEXTEND_TOK = 'BVZEROEXTEND';
  BVREPEAT_TOK = 'BVREPEAT';
  BVROTL_TOK = 'BVROTL';
  BVROTR_TOK = 'BVROTR';
  BVSLT_TOK = 'BVSLT';
  BVSGT_TOK = 'BVSGT';
  BVSLE_TOK = 'BVSLE';
  BVSGE_TOK = 'BVSGE';

  // Sets
  SETS_CHOOSE_TOK = 'CHOOSE';

  // Relations
  JOIN_TOK = 'JOIN';
  TRANSPOSE_TOK = 'TRANSPOSE';
  PRODUCT_TOK = 'PRODUCT';
  TRANSCLOSURE_TOK = 'TCLOSURE';
  IDEN_TOK = 'IDEN';
  JOIN_IMAGE_TOK = 'JOIN_IMAGE';

  // Strings
  STRING_TOK = 'STRING';
  STRING_CONCAT_TOK = 'CONCAT';
  STRING_LENGTH_TOK = 'LENGTH';
  STRING_CONTAINS_TOK = 'CONTAINS';
  STRING_SUBSTR_TOK = 'SUBSTR';
  STRING_CHARAT_TOK = 'CHARAT';
  STRING_INDEXOF_TOK = 'INDEXOF';
  STRING_REPLACE_TOK = 'REPLACE';
  STRING_REPLACE_ALL_TOK = 'REPLACE_ALL';
  STRING_PREFIXOF_TOK = 'PREFIXOF';
  STRING_SUFFIXOF_TOK = 'SUFFIXOF';
  STRING_STOI_TOK = 'STRING_TO_INTEGER';
  STRING_ITOS_TOK = 'INTEGER_TO_STRING';
  STRING_TO_REGEXP_TOK = 'STRING_TO_REGEXP';
  STRING_TOLOWER_TOK = 'TOLOWER';
  STRING_TOUPPER_TOK = 'TOUPPER';
  STRING_REV_TOK = 'REVERSE';
  REGEXP_CONCAT_TOK = 'RE_CONCAT';
  REGEXP_UNION_TOK = 'RE_UNION';
  REGEXP_INTER_TOK = 'RE_INTER';
  REGEXP_STAR_TOK = 'RE_STAR';
  REGEXP_PLUS_TOK = 'RE_PLUS';
  REGEXP_OPT_TOK = 'RE_OPT';
  REGEXP_RANGE_TOK = 'RE_RANGE';
  REGEXP_LOOP_TOK = 'RE_LOOP';
  REGEXP_EMPTY_TOK = 'RE_EMPTY';
  REGEXP_SIGMA_TOK = 'RE_SIGMA';
  REGEXP_COMPLEMENT_TOK = 'RE_COMPLEMENT';
  SEQ_UNIT_TOK = 'SEQ_UNIT';

  SETS_CARD_TOK = 'CARD';

  FMF_CARD_TOK = 'HAS_CARD';
  UNIVSET_TOK = 'UNIVERSE';

  // these are parsed by special NUMBER_OR_RANGEOP rule, below
  DECIMAL_LITERAL;
  INTEGER_LITERAL;
  DOT;
  DOTDOT;
}/* tokens */

@parser::members {

// Idea and code guidance from Sam Harwell,
// http://www.antlr.org/wiki/display/ANTLR3/Operator+precedence+parser

bool isRightToLeft(int type) {
  // return true here for any operators that are right-to-left associative
  switch(type) {
  case IMPLIES_TOK: return true;
  default: return false;
  }
}/* isRightToLeft() */

int getOperatorPrecedence(int type) {
  switch(type) {
  case BITVECTOR_TOK: return 1;
  //case DOT:
  case LPAREN:
  case LBRACE: return 2;
  case LBRACKET: return 3;
  case ARROW_TOK: return 4;
  case IS_INTEGER_TOK: return 5;
  case BVSLT_TOK:
  case BVSLE_TOK:
  case BVSGT_TOK:
  case BVSGE_TOK: return 6;
  case BVLT_TOK:
  case BVLE_TOK:
  case BVGT_TOK:
  case BVGE_TOK: return 7;
  case LEFTSHIFT_TOK:
  case RIGHTSHIFT_TOK: return 8;
  case SX_TOK:
  case BVZEROEXTEND_TOK:
  case BVREPEAT_TOK:
  case BVROTL_TOK:
  case BVROTR_TOK: return 9;
  case BVUDIV_TOK:
  case BVSDIV_TOK:
  case BVUREM_TOK:
  case BVSREM_TOK:
  case BVSMOD_TOK:
  case BVSHL_TOK:
  case BVASHR_TOK:
  case BVLSHR_TOK: return 10;
  case BVUMINUS_TOK:
  case BVPLUS_TOK:
  case BVSUB_TOK: return 11;
  case BVNEG_TOK: return 12;
  case BVXNOR_TOK: return 13;
  case BVNOR_TOK:
  case BVCOMP_TOK: return 14;
  case BVNAND_TOK: return 15;
  case BVXOR_TOK: return 16;
  case BVAND_TOK: return 17;
  case BAR: return 18;
  case CONCAT_TOK: return 19;
//case UMINUS_TOK: return 20;
  case WITH_TOK: return 21;
  case EXP_TOK: return 22;
  case STAR_TOK:
  case INTDIV_TOK:
  case DIV_TOK:
  case TUPLE_TOK:
  case MOD_TOK: return 23;
  case PLUS_TOK:
  case MINUS_TOK:
  case JOIN_TOK:
  case TRANSPOSE_TOK:
  case PRODUCT_TOK:
  case IDEN_TOK:
  case JOIN_IMAGE_TOK:
  case TRANSCLOSURE_TOK:
  case SETS_CHOOSE_TOK: return 24;
  case LEQ_TOK:
  case LT_TOK:
  case GEQ_TOK:
  case GT_TOK:
  case MEMBER_TOK:
  case SETS_CARD_TOK:
  case FMF_CARD_TOK: return 25;
  case EQUAL_TOK:
  case DISEQUAL_TOK: return 26;
  case NOT_TOK: return 27;
  case AND_TOK: return 28;
  case OR_TOK:
  case XOR_TOK: return 29;
  case IMPLIES_TOK: return 30;// right-to-left
  case IFF_TOK: return 31;
  case FORALL_TOK:
  case EXISTS_TOK:return 32;
  case ASSIGN_TOK:
  case IN_TOK: return 33;

  default:
    std::stringstream ss;
    ss << "internal error: no entry in precedence table for operator " << CvcParserTokenNames[type];
    throw ParserException(ss.str());
  }
}/* getOperatorPrecedence() */

api::Kind getOperatorKind(int type, bool& negate) {
  negate = false;

  switch(type) {
    // booleanBinop
  case IFF_TOK: return api::EQUAL;
  case IMPLIES_TOK: return api::IMPLIES;
  case OR_TOK: return api::OR;
  case XOR_TOK: return api::XOR;
  case AND_TOK: return api::AND;

  case SETS_CHOOSE_TOK: return api::CHOOSE;
  case PRODUCT_TOK: return api::PRODUCT;
  case JOIN_TOK: return api::JOIN;
  case JOIN_IMAGE_TOK: return api::JOIN_IMAGE;


    // comparisonBinop
  case EQUAL_TOK: return api::EQUAL;
  case DISEQUAL_TOK: negate = true; return api::EQUAL;
  case GT_TOK: return api::GT;
  case GEQ_TOK: return api::GEQ;
  case LT_TOK: return api::LT;
  case LEQ_TOK: return api::LEQ;
  case MEMBER_TOK: return api::MEMBER;
  case SETS_CARD_TOK: return api::CARD;
  case FMF_CARD_TOK: return api::CARDINALITY_CONSTRAINT;

    // arithmeticBinop
  case PLUS_TOK: return api::PLUS;
  case MINUS_TOK: return api::MINUS;
  case STAR_TOK: return api::MULT;
  case INTDIV_TOK: return api::INTS_DIVISION;
  case MOD_TOK: return api::INTS_MODULUS;
  case DIV_TOK: return api::DIVISION;
  case EXP_TOK: return api::POW;

    // bvBinop
  case CONCAT_TOK: return api::BITVECTOR_CONCAT;
  case BAR: return api::BITVECTOR_OR;
  case BVAND_TOK: return api::BITVECTOR_AND;

  }

  std::stringstream ss;
  ss << "internal error: no entry in operator-kind table for operator " << CvcParserTokenNames[type];
  throw ParserException(ss.str());

}/* getOperatorKind() */

unsigned findPivot(const std::vector<unsigned>& operators,
                   unsigned startIndex, unsigned stopIndex) {
  unsigned pivot = startIndex;
  unsigned pivotRank = getOperatorPrecedence(operators[pivot]);
  /*Debug("prec") << "initial pivot at " << pivot
                << "(" << CvcParserTokenNames[operators[pivot]] << ") "
                << "level " << pivotRank << std::endl;*/
  for(unsigned i = startIndex + 1; i <= stopIndex; ++i) {
    unsigned current = getOperatorPrecedence(operators[i]);
    bool rtl = isRightToLeft(operators[i]);
    if(current > pivotRank || (current == pivotRank && !rtl)) {
      /*Debug("prec") << "new pivot at " << i
                    << "(" << CvcParserTokenNames[operators[i]] << ") "
                    << "level " << current << " rtl == " << rtl << std::endl;*/
      pivot = i;
      pivotRank = current;
    }
  }
  return pivot;
}/* findPivot() */

CVC4::api::Term createPrecedenceTree(Parser* parser, api::Solver* solver,
                          const std::vector<CVC4::api::Term>& expressions,
                          const std::vector<unsigned>& operators,
                          unsigned startIndex, unsigned stopIndex) {
  assert(expressions.size() == operators.size() + 1);
  assert(startIndex < expressions.size());
  assert(stopIndex < expressions.size());
  assert(startIndex <= stopIndex);

  if(stopIndex == startIndex) {
    return expressions[startIndex];
  }

  unsigned pivot = findPivot(operators, startIndex, stopIndex - 1);
  //Debug("prec") << "pivot[" << startIndex << "," << stopIndex - 1 << "] at " << pivot << std::endl;
  bool negate;
  api::Kind k = getOperatorKind(operators[pivot], negate);
  CVC4::api::Term lhs = createPrecedenceTree(
      parser, solver, expressions, operators, startIndex, pivot);
  CVC4::api::Term rhs = createPrecedenceTree(
      parser, solver, expressions, operators, pivot + 1, stopIndex);

  if (lhs.getSort().isSet())
  {
    switch (k)
    {
      case api::LEQ: k = api::SUBSET; break;
      case api::MINUS: k = api::SETMINUS; break;
      case api::BITVECTOR_AND: k = api::INTERSECTION; break;
      case api::BITVECTOR_OR: k = api::UNION; break;
      default: break;
    }
  }
  else if (lhs.getSort().isString())
  {
    switch (k)
    {
      case api::MEMBER: k = api::STRING_IN_REGEXP; break;
      default: break;
    }
  }

  api::Term e = solver->mkTerm(k, lhs, rhs);
  return negate ? e.notTerm() : e;
}/* createPrecedenceTree() recursive variant */

api::Term createPrecedenceTree(Parser* parser, api::Solver* s,
                          const std::vector<CVC4::api::Term>& expressions,
                          const std::vector<unsigned>& operators) {
  if(Debug.isOn("prec") && operators.size() > 1) {
    for(unsigned i = 0; i < expressions.size(); ++i) {
      Debug("prec") << expressions[i];
      if(operators.size() > i) {
        Debug("prec") << ' ' << CvcParserTokenNames[operators[i]] << ' ';
      }
    }
    Debug("prec") << std::endl;
  }

  api::Term e = createPrecedenceTree(
      parser, s, expressions, operators, 0, expressions.size() - 1);
  if(Debug.isOn("prec") && operators.size() > 1) {
    language::SetLanguage::Scope ls(Debug("prec"), language::output::LANG_AST);
    Debug("prec") << "=> " << e << std::endl;
  }
  return e;
}/* createPrecedenceTree() base variant */

/** Add n NOTs to the front of e and return the result. */
api::Term addNots(api::Solver* s, size_t n, api::Term e) {
  while(n-- > 0) {
    e = e.notTerm();
  }
  return e;
}/* addNots() */

}/* @parser::members */

@header {
/**
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.
 **/
}/* @header */

@lexer::includes {

/** This suppresses warnings about the redefinition of token symbols between different
  * parsers. The redefinitions should be harmless as long as no client: (a) #include's
  * the lexer headers for two grammars AND (b) uses the token symbol definitions. */
#pragma GCC system_header

#if defined(CVC4_COMPETITION_MODE) && !defined(CVC4_SMTCOMP_APPLICATION_TRACK)
/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#  define ANTLR3_INLINE_INPUT_ASCII
#  define ANTLR3_INLINE_INPUT_8BIT
#endif /* CVC4_COMPETITION_MODE && !CVC4_SMTCOMP_APPLICATION_TRACK */

#include "parser/antlr_input.h"
#include "parser/antlr_tracing.h"
#include "parser/parser.h"
#include "util/integer.h"

}/* @lexer::includes */

@parser::includes {

#include <cassert>
#include <memory>
#include <stdint.h>

#include "options/set_language.h"
#include "parser/antlr_tracing.h"
#include "parser/parser.h"
#include "smt/command.h"

namespace CVC4 {
  class Expr;
}/* CVC4 namespace */

}/* @parser::includes */

@parser::postinclude {

#include <sstream>
#include <string>
#include <vector>

#include "base/output.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"


#define REPEAT_COMMAND(k, CommandCtor)                      \
  ({                                                        \
    unsigned __k = (k);                                     \
    (__k <= 1)                                              \
      ? (Command*) new CommandCtor                          \
      : ({                                                  \
          CommandSequence* __seq = new CommandSequence();   \
          while(__k-- > 0) {                                \
            __seq->addCommand(new CommandCtor);             \
          }                                                 \
          (Command*) __seq;                                 \
        });                                                 \
  })

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Parser*)PARSER->super)
#undef SOLVER
#define SOLVER PARSER_STATE->getSolver()
#undef MK_TERM
#define MK_TERM SOLVER->mkTerm
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

#define ENSURE_BV_SIZE(k, f)                                   \
{                                                              \
  unsigned size = f.getSort().getBVSize();        \
  if(k > size) {                                               \
    f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_ZERO_EXTEND,k - size), f); \
  } else if (k < size) {                                       \
    f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_EXTRACT, k - 1, 0), f); \
  }                                                            \
}

}/* @parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::api::Term expr = CVC4::api::Term()]
  : formula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd_return = NULL]
@declarations {
    std::unique_ptr<CVC4::Command> cmd;
}
@after {
    cmd_return = cmd.release();
}
  : c=command[&cmd]
  | LPAREN IDENTIFIER
    { std::string s = AntlrInput::tokenText($IDENTIFIER);
    if(s == "benchmark") {
        PARSER_STATE->parseError(
            "In CVC4 presentation language mode, but SMT-LIBv1 format "
            "detected, which is not supported anymore.");
      } else if(s == "set" || s == "get" || s == "declare" ||
                s == "define" || s == "assert") {
        PARSER_STATE->parseError(
            "In CVC4 presentation language mode, but SMT-LIB format detected. "
            "Use --lang smt for SMT-LIB support.");
      } else {
        PARSER_STATE->parseError(
            "A CVC4 presentation language command cannot begin with a "
            "parenthesis; expected command name.");
      }
    }
  | EOF
  ;

/**
 * Matches a command of the input. If a declaration, it will return an empty
 * command.
 */
command [std::unique_ptr<CVC4::Command>* cmd]
  : ( mainCommand[cmd] SEMICOLON
    | SEMICOLON
    | LET_TOK { PARSER_STATE->pushScope(); }
      typeOrVarLetDecl[CHECK_DECLARED] (
          COMMA typeOrVarLetDecl[CHECK_DECLARED] )*
      IN_TOK command[cmd]
      { PARSER_STATE->popScope(); }
    )
    { if(!(*cmd)) {
        cmd->reset(new EmptyCommand());
      }
    }
  | IDENTIFIER SEMICOLON
    { std::stringstream ss;
      ss << "Unrecognized command `"
         << AntlrInput::tokenText($IDENTIFIER)
         << "'";
      PARSER_STATE->parseError(ss.str());
    }
  ;

typeOrVarLetDecl[CVC4::parser::DeclarationCheck check]
options { backtrack = true; }
  : letDecl | typeLetDecl[check]
  ;

mainCommand[std::unique_ptr<CVC4::Command>* cmd]
@init {
  api::Term f;
  SExpr sexpr;
  std::string id;
  api::Sort t;
  std::vector<CVC4::api::DatatypeDecl> dts;
  Debug("parser-extra") << "command: " << AntlrInput::tokenText(LT(1)) << std::endl;
  std::string s;
  api::Term func;
  std::vector<api::Term> bvs;
  std::vector<api::Term> funcs;
  std::vector<api::Term> formulas;
  std::vector<std::vector<api::Term>> formals;
  std::vector<std::string> ids;
  std::vector<CVC4::api::Sort> types;
  bool idCommaFlag = true;
  bool formCommaFlag = true;
}
    /* our bread & butter */
  : ASSERT_TOK formula[f] { cmd->reset(new AssertCommand(f.getExpr())); }

  | QUERY_TOK formula[f] { cmd->reset(new QueryCommand(f.getExpr())); }
  | CHECKSAT_TOK formula[f]?
    {
      cmd->reset(f.isNull() ? new CheckSatCommand()
                            : new CheckSatCommand(f.getExpr()));
    }
    /* options */
  | OPTION_TOK
    ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
    ( symbolicExpr[sexpr]
      { if(s == "logic") {
          cmd->reset(new SetBenchmarkLogicCommand(sexpr.getValue()));
        } else {
          cmd->reset(new SetOptionCommand(s, sexpr));
        }
      }
    | TRUE_TOK { cmd->reset(new SetOptionCommand(s, SExpr("true"))); }
    | FALSE_TOK { cmd->reset(new SetOptionCommand(s, SExpr("false"))); }
    | { cmd->reset(new SetOptionCommand(s, SExpr("true"))); }
    )

    /* push / pop */
  | PUSH_TOK ( k=numeral { cmd->reset(REPEAT_COMMAND(k, PushCommand())); }
               | { cmd->reset(new PushCommand()); } )
  | POP_TOK ( k=numeral { cmd->reset(REPEAT_COMMAND(k, PopCommand())); }
              | { cmd->reset(new PopCommand()); } )
  | POPTO_TOK k=numeral?
    { UNSUPPORTED("POPTO command"); }

    /* push / pop scopes */
  | PUSH_SCOPE_TOK k=numeral?
    { UNSUPPORTED("PUSH_SCOPE command"); }
  | POP_SCOPE_TOK k=numeral?
    { UNSUPPORTED("POP_SCOPE command"); }
  | POPTO_SCOPE_TOK k=numeral?
    { UNSUPPORTED("POPTO_SCOPE command"); }

  | RESET_TOK
    { cmd->reset(new ResetCommand());
      PARSER_STATE->reset();
    }

  | RESET_TOK ASSERTIONS_TOK
    { cmd->reset(new ResetAssertionsCommand());
      PARSER_STATE->reset();
    }

    // Datatypes can be mututally-recursive if they're in the same
    // definition block, separated by a comma.  So we parse everything
    // and then ask the ExprManager to resolve everything in one go.
  | DATATYPE_TOK
    { /* open a scope to keep the UnresolvedTypes contained */
      PARSER_STATE->pushScope(); }
    datatypeDef[dts]
    ( COMMA datatypeDef[dts] )*
    END_TOK
    { PARSER_STATE->popScope();
      cmd->reset(new DatatypeDeclarationCommand(
          api::sortVectorToTypes(PARSER_STATE->bindMutualDatatypeTypes(dts))));
    }

  | CONTEXT_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { UNSUPPORTED("CONTEXT command"); }
    | { UNSUPPORTED("CONTEXT command"); }
    )

  | FORGET_TOK identifier[id,CHECK_NONE,SYM_VARIABLE]
    { UNSUPPORTED("FORGET command"); }

  | GET_TYPE_TOK formula[f]
    { UNSUPPORTED("GET_TYPE command"); }

  | CHECK_TYPE_TOK formula[f] COLON type[t,CHECK_DECLARED]
    { UNSUPPORTED("CHECK_TYPE command"); }

  | GET_CHILD_TOK formula[f] k=numeral
    { UNSUPPORTED("GET_CHILD command"); }

  | GET_OP_TOK formula[f]
    { UNSUPPORTED("GET_OP command"); }

  | GET_VALUE_TOK formula[f]
    { cmd->reset(new GetValueCommand(f.getExpr())); }

  | SUBSTITUTE_TOK identifier[id,CHECK_NONE,SYM_VARIABLE] COLON
    type[t,CHECK_DECLARED] EQUAL_TOK formula[f] LBRACKET
    identifier[id,CHECK_NONE,SYM_VARIABLE] ASSIGN_TOK formula[f] RBRACKET
    { UNSUPPORTED("SUBSTITUTE command"); }

    /* Like the --debug command line option, DBG turns on both tracing
     * and debugging. */
  | DBG_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Debug.on(s); Trace.on(s); }
    | { Message() << "Please specify what to debug." << std::endl; }
    )

  | TRACE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Trace.on(s); }
    | { Message() << "Please specify something to trace." << std::endl; }
    )
  | UNTRACE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Trace.off(s); }
    | { Message() << "Please specify something to untrace." << std::endl; }
    )

  | HELP_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { Message() << "No help available for `" << s << "'." << std::endl; }
  |   { Message() << "Please use --help at the command line for help."
                << std::endl; }
            )

  | TRANSFORM_TOK formula[f]
    { cmd->reset(new SimplifyCommand(f.getExpr())); }

  | PRINT_TOK formula[f]
    { UNSUPPORTED("PRINT command"); }
  | PRINT_TYPE_TOK type[t,CHECK_DECLARED]
    { UNSUPPORTED("PRINT_TYPE command"); }

  | CALL_TOK identifier[id,CHECK_NONE,SYM_VARIABLE] formula[f]
    { UNSUPPORTED("CALL command"); }

  | ECHO_TOK
    ( simpleSymbolicExpr[sexpr]
      { cmd->reset(new EchoCommand(sexpr.getValue())); }
    | { cmd->reset(new EchoCommand()); }
    )

  | EXIT_TOK
    { cmd->reset(new QuitCommand()); }

  | INCLUDE_TOK
    ( ( str[s] | IDENTIFIER { s = AntlrInput::tokenText($IDENTIFIER); } )
      { UNSUPPORTED("INCLUDE command"); }
    | { PARSER_STATE->parseError("No filename given to INCLUDE command"); }
    )

  | DUMP_PROOF_TOK
    { cmd->reset(new GetProofCommand()); }

  | DUMP_UNSAT_CORE_TOK
    { cmd->reset(new GetUnsatCoreCommand()); }

  | ( DUMP_ASSUMPTIONS_TOK
    | DUMP_SIG_TOK
    | DUMP_TCC_TOK
    | DUMP_TCC_ASSUMPTIONS_TOK
    | DUMP_TCC_PROOF_TOK
    | DUMP_CLOSURE_TOK
    | DUMP_CLOSURE_PROOF_TOK
    ) { UNSUPPORTED("DUMP* command"); }

    /* these are all synonyms */
  | ( WHERE_TOK | ASSERTIONS_TOK | ASSUMPTIONS_TOK )
    { cmd->reset(new GetAssertionsCommand()); }

  | COUNTEREXAMPLE_TOK
    { cmd->reset(new GetModelCommand); }
  | COUNTERMODEL_TOK
    { cmd->reset(new GetModelCommand); }

  | ARITH_VAR_ORDER_TOK LPAREN formula[f] ( COMMA formula[f] )* RPAREN
    { UNSUPPORTED("ARITH_VAR_ORDER command"); }

  | CONTINUE_TOK
    { UNSUPPORTED("CONTINUE command"); }
  | RESTART_TOK formula[f] { UNSUPPORTED("RESTART command"); }
  | RECURSIVE_FUNCTION_TOK (identifier[id,CHECK_NONE,SYM_VARIABLE]
    {
      if(idCommaFlag){
        idCommaFlag=false;
      }
      else{
        PARSER_STATE->parseError("Identifiers need to be comma separated");
      }
    }
    COLON type[t,CHECK_DECLARED] (COMMA {
      idCommaFlag=true;
      })?
    {
      func = PARSER_STATE->bindVar(id, t, ExprManager::VAR_FLAG_NONE, true);
      ids.push_back(id);
      types.push_back(t);
      funcs.push_back(func);
    })+
    EQUAL_TOK (formula[f]
    {
      if(formCommaFlag){
        formCommaFlag=false;
      }
      else{
        PARSER_STATE->parseError("Function definitions need to be comma separated");
      }
    }
    (COMMA{
      formCommaFlag=true;
    })?
    {
      if( f.getKind()==api::LAMBDA ){
        bvs.insert(bvs.end(), f[0].begin(), f[0].end());
        formals.push_back(bvs);
        bvs.clear();
        f = f[1];
        formulas.push_back(f);
      }
      else {
        formals.push_back(bvs);
        formulas.push_back(f);
      }
    })+
    {
      if(idCommaFlag){
        PARSER_STATE->parseError("Cannot end function list with comma");
      }
      if(formCommaFlag){
        PARSER_STATE->parseError("Cannot end function definition list with comma");
      }
      if(funcs.size()!=formulas.size()){
        PARSER_STATE->parseError("Number of functions doesn't match number of function definitions");
      }
      for(unsigned int i = 0, size = funcs.size(); i < size; i++){
        if(!funcs[i].getSort().isSubsortOf(types[i])){
          PARSER_STATE->parseError("Type mismatch in definition");
        }
      }
      cmd->reset(
          new DefineFunctionRecCommand(SOLVER, funcs, formals, formulas, true));
    }
  | toplevelDeclaration[cmd]
  ;

simpleSymbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::string s;
  CVC4::Rational r;
}
  : INTEGER_LITERAL
    { sexpr = SExpr(Integer(AntlrInput::tokenText($INTEGER_LITERAL))); }
  | MINUS_TOK INTEGER_LITERAL
    { sexpr = SExpr(-Integer(AntlrInput::tokenText($INTEGER_LITERAL))); }
  | DECIMAL_LITERAL
    { sexpr = SExpr(AntlrInput::tokenToRational($DECIMAL_LITERAL)); }
  | HEX_LITERAL
    { sexpr = SExpr(AntlrInput::tokenText($HEX_LITERAL)); }
  | BINARY_LITERAL
    { sexpr = SExpr(AntlrInput::tokenText($BINARY_LITERAL)); }
  | str[s]
    { sexpr = SExpr(s); }
  | IDENTIFIER
    { sexpr = SExpr(AntlrInput::tokenText($IDENTIFIER)); }
  ;

symbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::vector<SExpr> children;
}
  : simpleSymbolicExpr[sexpr]
  | LPAREN (symbolicExpr[sexpr] { children.push_back(sexpr); } )* RPAREN
    { sexpr = SExpr(children); }
  ;

/**
 * Match a top-level declaration.
 */
toplevelDeclaration[std::unique_ptr<CVC4::Command>* cmd]
@init {
  std::vector<std::string> ids;
  api::Sort t;
  Debug("parser-extra") << "declaration: " << AntlrInput::tokenText(LT(1))
                        << std::endl;
}
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON
    ( declareVariables[cmd,t,ids,true]
    | declareTypes[cmd,ids] )
  ;

/**
 * A bound variable declaration.
 */
boundVarDecl[std::vector<std::string>& ids, CVC4::api::Sort& t]
@init {
  std::unique_ptr<Command> local_cmd;
}
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON
    declareVariables[&local_cmd,t,ids,false]
  ;

/**
 * A series of bound variable declarations.
 */
boundVarDecls
@init {
  std::vector<std::string> ids;
  api::Sort t;
}
  : boundVarDecl[ids,t] ( COMMA boundVarDecl[ids,t] )*
  ;

boundVarDeclsReturn[std::vector<CVC4::api::Term>& terms,
                    std::vector<CVC4::api::Sort>& types]
@init {
  std::vector<std::string> ids;
  api::Sort t;
  terms.clear();
  types.clear();
}
  : boundVarDeclReturn[terms,types] ( COMMA boundVarDeclReturn[terms,types] )*
  ;

boundVarDeclReturn[std::vector<CVC4::api::Term>& terms,
                   std::vector<CVC4::api::Sort>& types]
@init {
  std::vector<std::string> ids;
  api::Sort t;
  // NOTE: do not clear the vectors here!
}
  : identifierList[ids,CHECK_NONE,SYM_VARIABLE] COLON type[t,CHECK_DECLARED]
    { const std::vector<api::Term>& vars = PARSER_STATE->bindBoundVars(ids, t);
      terms.insert(terms.end(), vars.begin(), vars.end());
      for(unsigned i = 0; i < vars.size(); ++i) {
        types.push_back(t);
      }
    }
  ;

/**
 * Match the right-hand-side of a type declaration.  Unlike
 * declareVariables[] below, don't need to return the Type, since it's
 * always the KindType (the type of types).  Also don't need toplevel
 * because type declarations are always top-level, except for
 * type-lets, which don't use this rule.
 */
declareTypes[std::unique_ptr<CVC4::Command>* cmd,
             const std::vector<std::string>& idList]
@init {
  api::Sort t;
}
    /* A sort declaration (e.g., "T : TYPE") */
  : TYPE_TOK
    { std::unique_ptr<DeclarationSequence> seq(new DeclarationSequence());
      for(std::vector<std::string>::const_iterator i = idList.begin();
          i != idList.end(); ++i) {
        // Don't allow a type variable to clash with a previously
        // declared type variable, however a type variable and a
        // non-type variable can clash unambiguously.  Break from CVC3
        // behavior here.
        PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_SORT);
        api::Sort sort = PARSER_STATE->mkSort(*i);
        Command* decl = new DeclareTypeCommand(*i, 0, sort.getType());
        seq->addCommand(decl);
      }
      cmd->reset(seq.release());
    }

    /* A type alias "T : TYPE = foo..." */
  | TYPE_TOK EQUAL_TOK type[t,CHECK_DECLARED]
    { for(std::vector<std::string>::const_iterator i = idList.begin();
          i != idList.end();
          ++i) {
        PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_SORT);
        PARSER_STATE->defineType(*i, t);
      }
    }
  ;

/**
 * Match the right-hand side of a variable declaration.  Returns the
 * type.  Some IDs might have been declared previously, and are not
 * re-declared if topLevel is true (CVC allows re-declaration if the
 * types are compatible---if they aren't compatible, an error is
 * thrown).  Also if topLevel is true, variable definitions are
 * permitted and "cmd" is output.  If topLevel is false, bound vars
 * are created
 */
declareVariables[std::unique_ptr<CVC4::Command>* cmd, CVC4::api::Sort& t,
                 const std::vector<std::string>& idList, bool topLevel]
@init {
  api::Term f;
  Debug("parser-extra") << "declType: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
    /* A variable declaration (or definition) */
  : type[t,CHECK_DECLARED] ( EQUAL_TOK formula[f] )?
    { std::unique_ptr<DeclarationSequence> seq;
      if(topLevel) {
        seq.reset(new DeclarationSequence());
      }
      if(f.isNull()) {
        Debug("parser") << "working on " << idList.front() << " : " << t
                        << std::endl;
        // CVC language allows redeclaration of variables if types are the same
        for(std::vector<std::string>::const_iterator i = idList.begin(),
              i_end = idList.end();
            i != i_end;
            ++i) {
          if(PARSER_STATE->isDeclared(*i, SYM_VARIABLE)) {
            api::Sort oldType = PARSER_STATE->getVariable(*i).getSort();
            Debug("parser") << "  " << *i << " was declared previously "
                            << "with type " << oldType << std::endl;
            if(oldType != t) {
              std::stringstream ss;
              ss << language::SetLanguage(language::output::LANG_CVC4)
                 << "incompatible type for `" << *i << "':" << std::endl
                 << "  old type: " << oldType << std::endl
                 << "  new type: " << t << std::endl;
              PARSER_STATE->parseError(ss.str());
            } else {
              Debug("parser") << "  types " << t << " and " << oldType
                              << " are compatible" << std::endl;
            }
          } else {
            Debug("parser") << "  " << *i << " not declared" << std::endl;
            if(topLevel) {
              api::Term func =
                  PARSER_STATE->bindVar(*i, t, ExprManager::VAR_FLAG_GLOBAL);
              Command* decl =
                  new DeclareFunctionCommand(*i, func.getExpr(), t.getType());
              seq->addCommand(decl);
            } else {
              PARSER_STATE->bindBoundVar(*i, t);
            }
          }
        }
      } else {
        // f is not null-- meaning this is a definition not a declaration
        //Check if the formula f has the correct type, declared as t.
        if(!f.getSort().isSubsortOf(t)){
          PARSER_STATE->parseError("Type mismatch in definition");
        }
        if(!topLevel) {
          // must be top-level; doesn't make sense to write something
          // like e.g. FORALL(x:INT = 4): [...]
          PARSER_STATE->parseError("cannot construct a definition here; maybe you want a LET");
        }
        assert(!idList.empty());
        for(std::vector<std::string>::const_iterator i = idList.begin(),
              i_end = idList.end();
            i != i_end;
            ++i) {
          Debug("parser") << "making " << *i << " : " << t << " = " << f << std::endl;
          PARSER_STATE->checkDeclaration(*i, CHECK_UNDECLARED, SYM_VARIABLE);
          api::Term func = PARSER_STATE->mkVar(
              *i,
              api::Sort(SOLVER, t.getType()),
              ExprManager::VAR_FLAG_GLOBAL | ExprManager::VAR_FLAG_DEFINED);
          PARSER_STATE->defineVar(*i, f);
          Command* decl =
              new DefineFunctionCommand(*i, func.getExpr(), f.getExpr(), true);
          seq->addCommand(decl);
        }
      }
      if(topLevel) {
        cmd->reset(new DeclarationSequence());
      }
    }
  ;

/**
 * Matches a list of identifiers separated by a comma and puts them in the
 * given list.
 * @param idList the list to fill with identifiers.
 * @param check what kinds of check to perform on the symbols
 */
identifierList[std::vector<std::string>& idList,
               CVC4::parser::DeclarationCheck check,
               CVC4::parser::SymbolType type]
@init {
  std::string id;
  idList.clear();
}
  : identifier[id,check,type] { idList.push_back(id); }
    ( COMMA identifier[id,check,type] { idList.push_back(id); } )*
  ;

/**
 * Matches an identifier and returns a string.
 */
identifier[std::string& id,
           CVC4::parser::DeclarationCheck check,
           CVC4::parser::SymbolType type]
  : IDENTIFIER
    { id = AntlrInput::tokenText($IDENTIFIER);
      PARSER_STATE->checkDeclaration(id, check, type); }
  ;

/**
 * Match the type in a declaration and do the declaration binding.  If
 * "check" is CHECK_NONE, then identifiers occurring in the type need
 * not exist!  They are created as "unresolved" types and linked up in
 * a type-substitution pass.  Right now, only datatype definitions are
 * supported in this way (since type names can occur without any
 * forward-declaration in CVC language datatype definitions, we have
 * to create types for them on-the-fly).  Before passing CHECK_NONE
 * you really should have a clear idea of WHY you need to parse that
 * way; then you should trace through Parser::bindMutualDatatypeType()
 * to figure out just what you're in for.
 */
type[CVC4::api::Sort& t,
     CVC4::parser::DeclarationCheck check]
@init {
  api::Sort t2;
  bool lhs;
  std::vector<api::Sort> args;
}
    /* a type, possibly a function */
  : restrictedTypePossiblyFunctionLHS[t,check,lhs]
    { if(lhs) {
        assert(t.isTuple());
        args = t.getTupleSorts();
      } else {
        args.push_back(t);
      }
    }
    ( ARROW_TOK type[t2,check] )?
    { if(t2.isNull()) {
        if(lhs) {
          PARSER_STATE->parseError("improperly-placed type list; expected `->' after to define a function; or else maybe these parentheses were meant to be square brackets, to define a tuple type?");
        }
      } else {
        t = SOLVER->mkFunctionSort(args, t2);
      }
    }

    /* type-lets: typeLetDecl defines the types, we just manage the
     * scopes here.  NOTE that LET in the CVC language is always
     * sequential! */
  | LET_TOK { PARSER_STATE->pushScope(); }
    typeLetDecl[check] ( COMMA typeLetDecl[check] )* IN_TOK type[t,check]
    { PARSER_STATE->popScope(); }
  ;

// A restrictedType is one that is not a "bare" function type (it can
// be enclosed in parentheses) and is not a type list.  To support the
// syntax
//
//   f : (nat, nat) -> nat;
//
// we have to permit restrictedTypes to be type lists (as on the LHS
// there).  The "type" rule above uses restictedTypePossiblyFunctionLHS
// directly in order to implement that; this rule allows a type list to
// parse but then issues an error.
restrictedType[CVC4::api::Sort& t,
               CVC4::parser::DeclarationCheck check]
@init {
  bool lhs;
}
  : restrictedTypePossiblyFunctionLHS[t,check,lhs]
    { if(lhs) { PARSER_STATE->parseError("improperly-placed type list; maybe these parentheses were meant to be square brackets, to define a tuple type?"); } }
  ;

/**
 * lhs is set to "true" on output if we have a list of types, so an
 * ARROW must follow.  An ARROW can always follow; lhs means it MUST.
 */
restrictedTypePossiblyFunctionLHS[CVC4::api::Sort& t,
                                  CVC4::parser::DeclarationCheck check,
                                  bool& lhs]
@init {
  api::Sort t2;
  api::Term f, f2;
  std::string id;
  std::vector<api::Sort> types;
  std::vector< std::pair<std::string, api::Sort> > typeIds;
  //SymbolTable* symtab;
  Parser* parser;
  lhs = false;
}
    /* named types */
  : identifier[id,check,SYM_SORT]
    parameterization[check,types]?
    {
      if(check == CHECK_DECLARED ||
         PARSER_STATE->isDeclared(id, SYM_SORT)) {
        Debug("parser-param") << "param: getSort " << id << " " << types.size() << " " << PARSER_STATE->getArity( id )
                              << " " << PARSER_STATE->isDeclared(id, SYM_SORT) << std::endl;
        if(types.size() != PARSER_STATE->getArity(id)) {
          std::stringstream ss;
          ss << "incorrect arity for symbol `" << id << "': expected "
             << PARSER_STATE->getArity( id ) << " type arguments, got "
             << types.size();
          PARSER_STATE->parseError(ss.str());
        }
        if(types.size() > 0) {
          t = PARSER_STATE->getSort(id, types);
        }else{
          t = PARSER_STATE->getSort(id);
        }
      } else {
        if(types.empty()) {
          t = PARSER_STATE->mkUnresolvedType(id);
          Debug("parser-param") << "param: make unres type " << id << std::endl;
        }else{
          t = PARSER_STATE->mkUnresolvedTypeConstructor(id,types);
          t = t.instantiate( types );
          Debug("parser-param") << "param: make unres param type " << id << " " << types.size() << " "
                                << PARSER_STATE->getArity( id ) << std::endl;
        }
      }
    }

    /* array types */
  | ARRAY_TOK restrictedType[t,check] OF_TOK restrictedType[t2,check]
    { t = SOLVER->mkArraySort(t, t2); }
  | SET_TOK OF_TOK restrictedType[t,check]
    { t = SOLVER->mkSetSort(t); }

    /* subtypes */
  | SUBTYPE_TOK LPAREN
    /* A bit tricky: this LAMBDA expression cannot refer to constants
     * declared in the outer context.  What follows isn't quite right,
     * though, since type aliases and function definitions should be
     * retained in the set of current declarations. */
    formula[f] ( COMMA formula[f2] )? RPAREN
    {
      PARSER_STATE->unimplementedFeature("predicate subtyping not supported in this release");
    }

    /* subrange types */
  | LBRACKET bound DOTDOT bound RBRACKET
    {
      PARSER_STATE->unimplementedFeature("subrange typing not supported in this release");
    }

    /* tuple types / old-style function types */
  | LBRACKET ( type[t,check] { types.push_back(t); }
    ( COMMA type[t,check] { types.push_back(t); } )* )? RBRACKET
    { if(types.size() == 1 && types.front().isFunction()) {
        // old style function syntax [ T -> U ]
        PARSER_STATE->parseError("old-style function type syntax not supported anymore; please use the new syntax");
      } else {
        // tuple type [ T, U, V... ]
        t = SOLVER->mkTupleSort(types);
      }
    }

    /* record types */
  | SQHASH ( identifier[id,CHECK_NONE,SYM_SORT] COLON type[t,check] { typeIds.push_back(std::make_pair(id, t)); }
    ( COMMA identifier[id,CHECK_NONE,SYM_SORT] COLON type[t,check] { typeIds.push_back(std::make_pair(id, t)); } )* )? HASHSQ
    { t = SOLVER->mkRecordSort(typeIds); }

    /* bitvector types */
  | BITVECTOR_TOK LPAREN k=numeral RPAREN
    { if(k == 0) {
        PARSER_STATE->parseError("Illegal bitvector size: 0");
      }
      t = SOLVER->mkBitVectorSort(k);
    }

    /* string type */
  | STRING_TOK { t = SOLVER->getStringSort(); }

    /* basic types */
  | BOOLEAN_TOK { t = SOLVER->getBooleanSort(); }
  | REAL_TOK { t = SOLVER->getRealSort(); }
  | INT_TOK { t = SOLVER->getIntegerSort(); }

    /* Parenthesized general type, or the lhs of an ARROW (a list of
     * types).  These two things are combined to avoid conflicts in
     * parsing. */
  | LPAREN type[t,check] { types.push_back(t); }
    ( COMMA type[t,check] { lhs = true; types.push_back(t); } )* RPAREN
    { if(lhs) { t = SOLVER->mkTupleSort(types); }
      // if !lhs, t is already set up correctly, nothing to do..
    }
  ;

parameterization[CVC4::parser::DeclarationCheck check,
                 std::vector<CVC4::api::Sort>& params]
@init {
  api::Sort t;
}
  : LBRACKET restrictedType[t,check] { Debug("parser-param") << "t = " << t << std::endl; params.push_back( t ); }
    ( COMMA restrictedType[t,check] { Debug("parser-param") << "t = " << t << std::endl; params.push_back( t ); } )* RBRACKET
  ;

bound
  : UNDERSCORE
  | integer
;

typeLetDecl[CVC4::parser::DeclarationCheck check]
@init {
  api::Sort t;
  std::string id;
}
  : identifier[id,CHECK_NONE,SYM_SORT] (COLON TYPE_TOK)? EQUAL_TOK restrictedType[t,check]
    { PARSER_STATE->defineType(id, t); }
  ;

/**
 * Matches a CVC4 expression.  Formulas and terms are not really
 * distinguished during parsing; please ignore the naming of the
 * grammar rules.
 *
 * @return the expression representing the formula/term
 */
formula[CVC4::api::Term& f]
@init {
  Debug("parser-extra") << "formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
  api::Term f2;
  std::vector<CVC4::api::Term> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : n=nots
    ( prefixFormula[f]
      { f = addNots(SOLVER, n, f); }
    | comparison[f]
      { f = addNots(SOLVER, n, f);
        expressions.push_back(f);
      }
      morecomparisons[expressions,operators]?
      {
        f = createPrecedenceTree(PARSER_STATE, SOLVER, expressions, operators);
      }
    )
  ;

morecomparisons[std::vector<CVC4::api::Term>& expressions,
                std::vector<unsigned>& operators] returns [size_t i = 0]
@init {
  unsigned op;
  api::Term f;
  $i = expressions.size();
}
  : booleanBinop[op] { operators.push_back(op); }
    n=nots
    ( prefixFormula[f]
      { expressions.push_back(addNots(SOLVER, n, f)); }
    | comparison[f]
      { f = addNots(SOLVER, n, f);
        expressions.push_back(f);
      }
      morecomparisons[expressions,operators]?
    )
  ;

/** Matches 0 or more NOTs. */
nots returns [size_t n = 0]
  : ( NOT_TOK { ++$n; } )*
  ;

prefixFormula[CVC4::api::Term& f]
@init {
  std::vector<std::string> ids;
  std::vector<api::Term> terms;
  std::vector<api::Sort> types;
  std::vector<api::Term> bvs;
  api::Sort t;
  api::Kind k;
  api::Term ipl;
}
    /* quantifiers */
  : ( FORALL_TOK { k = api::FORALL; } | EXISTS_TOK { k = api::EXISTS; } )
    { PARSER_STATE->pushScope(); } LPAREN
    boundVarDecl[ids,t]
    { for(std::vector<std::string>::const_iterator i = ids.begin(); i != ids.end(); ++i) {
        bvs.push_back(PARSER_STATE->bindBoundVar(*i, t));
      }
      ids.clear();
    }
    ( COMMA boundVarDecl[ids,t]
      {
        for(std::vector<std::string>::const_iterator i = ids.begin(); i != ids.end(); ++i) {
          bvs.push_back(PARSER_STATE->bindBoundVar(*i, t));
        }
        ids.clear();
      }
    )* RPAREN {
      terms.push_back( MK_TERM( api::BOUND_VAR_LIST, bvs ) ); }
    COLON instantiationPatterns[ipl]? formula[f]
    { PARSER_STATE->popScope();
      terms.push_back(f);
      if(! ipl.isNull()) {
        terms.push_back(ipl);
      }
      f = MK_TERM(k, terms);
    }

   /* lets: letDecl defines the variables and functionss, we just
     * manage the scopes here.  NOTE that LET in the CVC language is
     * always sequential! */
  | LET_TOK { PARSER_STATE->pushScope(); }
    letDecl ( COMMA letDecl )*
    IN_TOK formula[f] { PARSER_STATE->popScope(); }

   /* lambda */
  | LAMBDA_TOK { PARSER_STATE->pushScope(); } LPAREN
    boundVarDeclsReturn[terms,types]
    RPAREN COLON formula[f]
    { PARSER_STATE->popScope();
      api::Term bvl = MK_TERM( api::BOUND_VAR_LIST, terms );
      f = MK_TERM( api::LAMBDA, bvl, f );
    }
  ;

instantiationPatterns[ CVC4::api::Term& expr ]
@init {
  std::vector<api::Term> args;
  api::Term f;
  std::vector<api::Term> patterns;
}
  : ( PATTERN_TOK LPAREN formula[f] { args.push_back( f ); } (COMMA formula[f] { args.push_back( f ); } )* RPAREN COLON
      { patterns.push_back( MK_TERM( api::INST_PATTERN, args ) );
        args.clear();
      } )+
    { if(! patterns.empty()) {
       expr = MK_TERM( api::INST_PATTERN_LIST, patterns );
       }
    }
  ;

/**
 * Matches (and defines) a single LET declaration.
 */
letDecl
@init {
  api::Term e;
  std::string name;
}
  : identifier[name,CHECK_NONE,SYM_VARIABLE] EQUAL_TOK formula[e]
    {
      Debug("parser") << language::SetLanguage(language::output::LANG_CVC4)
                      << e.getSort() << std::endl;
      PARSER_STATE->defineVar(name, e);
      Debug("parser") << "LET[" << PARSER_STATE->scopeLevel() << "]: "
                      << name << std::endl
                      << " ==>" << " " << e << std::endl;
    }
  ;

booleanBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : IFF_TOK
  | IMPLIES_TOK
  | OR_TOK
  | XOR_TOK
  | AND_TOK
  ;

comparison[CVC4::api::Term& f]
@init {
  std::vector<CVC4::api::Term> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : term[f] { expressions.push_back(f); }
    ( comparisonBinop[op] term[f]
      { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(PARSER_STATE, SOLVER, expressions, operators); }
  ;

comparisonBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : EQUAL_TOK
  | DISEQUAL_TOK
  | GT_TOK
  | GEQ_TOK
  | LT_TOK
  | LEQ_TOK
  | MEMBER_TOK
  | FMF_CARD_TOK
  ;

arithmeticBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : PLUS_TOK
  | MINUS_TOK
  | STAR_TOK
  | INTDIV_TOK
  | MOD_TOK
  | DIV_TOK
  | EXP_TOK
  ;

/** Parses an array/tuple/record assignment term. */
term[CVC4::api::Term& f]
@init {
  std::vector<CVC4::api::Term> expressions;
  std::vector<unsigned> operators;
  unsigned op;
  api::Sort t;
}
  : uminusTerm[f]
    ( WITH_TOK
      ( arrayStore[f] ( COMMA arrayStore[f] )*
      | DOT ( tupleStore[f] ( COMMA DOT tupleStore[f] )*
            | recordStore[f] ( COMMA DOT recordStore[f] )* ) )
    | { expressions.push_back(f); }
      ( arithmeticBinop[op] uminusTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
      { f = createPrecedenceTree(PARSER_STATE, SOLVER, expressions, operators); }
    )
  ;

/**
 * Parses just part of the array assignment (and constructs
 * the store terms).
 */
arrayStore[CVC4::api::Term& f]
@init {
  api::Term f2, k;
}
  : LBRACKET formula[k] RBRACKET
    { f2 = MK_TERM(CVC4::api::SELECT, f, k); }
    ( ( arrayStore[f2]
      | DOT ( tupleStore[f2]
            | recordStore[f2] ) )
    | ASSIGN_TOK term[f2] )
    { f = MK_TERM(CVC4::api::STORE, f, k, f2); }
  ;

/**
 * Parses just part of the tuple assignment (and constructs
 * the store terms).
 */
tupleStore[CVC4::api::Term& f]
@init {
  api::Term f2;
}
  : k=numeral
    { api::Sort t = f.getSort();
      if(! t.isTuple()) {
        PARSER_STATE->parseError("tuple-update applied to non-tuple");
      }
      size_t length = t.getTupleLength();
      if(k >= length) {
        std::stringstream ss;
        ss << "tuple is of length " << length << "; cannot update index " << k;
        PARSER_STATE->parseError(ss.str());
      }
      const api::Datatype& dt = t.getDatatype();
      f2 = SOLVER->mkTerm(
          api::APPLY_SELECTOR, dt[0][k].getSelectorTerm(), f);
    }
    ( ( arrayStore[f2]
      | DOT ( tupleStore[f2]
            | recordStore[f2] ) )
    | ASSIGN_TOK term[f2] )
    { f = SOLVER->mkTerm(SOLVER->mkOp(api::TUPLE_UPDATE,k), f, f2); }
  ;

/**
 * Parses just part of the record assignment (and constructs
 * the store terms).
 */
recordStore[CVC4::api::Term& f]
@init {
  std::string id;
  api::Term f2;
}
  : identifier[id,CHECK_NONE,SYM_VARIABLE]
    { api::Sort t = f.getSort();
      if(! t.isRecord()) {
        std::stringstream ss;
        ss << "record-update applied to non-record term" << std::endl
           << "the term: " << f << std::endl
           << "its type: " << t;
        PARSER_STATE->parseError(ss.str());
      }
      const api::Datatype& dt = t.getDatatype();
      f2 = SOLVER->mkTerm(
          api::APPLY_SELECTOR, dt[0][id].getSelectorTerm(), f);
    }
    ( ( arrayStore[f2]
      | DOT ( tupleStore[f2]
            | recordStore[f2] ) )
    | ASSIGN_TOK term[f2] )
    { f = SOLVER->mkTerm(SOLVER->mkOp(api::RECORD_UPDATE,id), f, f2); }
  ;

/** Parses a unary minus term. */
uminusTerm[CVC4::api::Term& f]
@init {
  unsigned minusCount = 0;
}
    /* Unary minus */
  : (MINUS_TOK { ++minusCount; })* bvBinaryOpTerm[f]
    {
      while (minusCount > 0)
      {
        --minusCount;
        f = MK_TERM(CVC4::api::UMINUS, f);
      }
    };

/** Parses bitvectors.  Starts with binary operators @, &, and |. */
bvBinaryOpTerm[CVC4::api::Term& f]
@init {
  std::vector<CVC4::api::Term> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : bvNegTerm[f] { expressions.push_back(f); }
    ( bvBinop[op] bvNegTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(PARSER_STATE, SOLVER, expressions, operators); }
  ;
bvBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : CONCAT_TOK
  | BAR // bitwise OR
  | BVAND_TOK
  ;

bvNegTerm[CVC4::api::Term& f]
    /* BV neg */
  : BVNEG_TOK bvNegTerm[f]
    {
      f = f.getSort().isSet() ? MK_TERM(CVC4::api::COMPLEMENT, f)
                              : MK_TERM(CVC4::api::BITVECTOR_NOT, f);
    }
  | relationBinopTerm[f]
  ;

relationBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : JOIN_TOK
  | PRODUCT_TOK
  | JOIN_IMAGE_TOK
  ;

relationBinopTerm[CVC4::api::Term& f]
@init {
  std::vector<CVC4::api::Term> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : postfixTerm[f] { expressions.push_back(f); }
    ( relationBinop[op] postfixTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(PARSER_STATE, SOLVER, expressions, operators); }
  ;

/**
 * Parses an array select / bitvector extract / bitvector shift /
 * function or constructor application.  These are all parsed the same
 * way because they are all effectively post-fix operators and can
 * continue piling onto an expression.  Array selects and bitvector
 * extracts even share similar syntax with their use of [ square
 * brackets ], so we left-factor as much out as possible to make ANTLR
 * happy.
 */
postfixTerm[CVC4::api::Term& f]
@init {
  api::Term f2;
  bool extract = false, left = false;
  std::vector<api::Term> args;
  std::string id;
  api::Sort t;
}
  : ( relationTerm[f]
    ( /* array select / bitvector extract */
      LBRACKET
        ( formula[f2] { extract = false; }
        | k1=numeral COLON k2=numeral { extract = true; } )
      RBRACKET
      { if(extract) {
          /* bitvector extract */
          f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_EXTRACT,k1,k2), f);
        } else {
          /* array select */
          f = MK_TERM(CVC4::api::SELECT, f, f2);
        }
      }
      /* left- or right-shift */
    | ( LEFTSHIFT_TOK { left = true; }
      | RIGHTSHIFT_TOK { left = false; } ) k=numeral
      {
        if(left) {
          f = MK_TERM(api::BITVECTOR_CONCAT, f, SOLVER->mkBitVector(k));
        } else {
          unsigned bv_size = f.getSort().getBVSize();
          f = MK_TERM(api::BITVECTOR_CONCAT,
                      SOLVER->mkBitVector(k),
                      SOLVER->mkTerm(
                          SOLVER->mkOp(api::BITVECTOR_EXTRACT, bv_size - 1, k), f));
        }
      }

      /* function/constructor application */
    | LPAREN { args.push_back(f); }
      formula[f] { args.push_back(f); }
      ( COMMA formula[f] { args.push_back(f); } )* RPAREN
      {
        PARSER_STATE->checkFunctionLike(args.front());
        api::Kind kind = PARSER_STATE->getKindForFunction(args.front());
        Debug("parser") << "expr is " << args.front() << std::endl;
        Debug("parser") << "kind is " << kind << std::endl;
        f = SOLVER->mkTerm(kind,args);
      }

      /* record / tuple select */
    | DOT
      ( identifier[id,CHECK_NONE,SYM_VARIABLE]
        { api::Sort type = f.getSort();
          if(! type.isRecord()) {
            PARSER_STATE->parseError("record-select applied to non-record");
          }
          const api::Datatype& dt = type.getDatatype();
          f = SOLVER->mkTerm(api::APPLY_SELECTOR,
                             dt[0][id].getSelectorTerm(),
                             f);
        }
      | k=numeral
        {
          api::Sort type = f.getSort();
          if(! type.isTuple()) {
            PARSER_STATE->parseError("tuple-select applied to non-tuple");
          }
          size_t length = type.getTupleLength();
          if(k >= length) {
            std::stringstream ss;
            ss << "tuple is of length " << length << "; cannot access index " << k;
            PARSER_STATE->parseError(ss.str());
          }
          const api::Datatype& dt = type.getDatatype();
          f = SOLVER->mkTerm(api::APPLY_SELECTOR,
                             dt[0][k].getSelectorTerm(),
                             f);
        }
      )
    )*
    | FLOOR_TOK LPAREN formula[f] RPAREN
      { f = MK_TERM(CVC4::api::TO_INTEGER, f); }
    | IS_INTEGER_TOK LPAREN formula[f] RPAREN
      { f = MK_TERM(CVC4::api::IS_INTEGER, f); }
    | ABS_TOK LPAREN formula[f] RPAREN
      { f = MK_TERM(CVC4::api::ABS, f); }
    | DIVISIBLE_TOK LPAREN formula[f] COMMA n=numeral RPAREN
      { f = MK_TERM(SOLVER->mkOp(CVC4::api::DIVISIBLE, n), f); }
    | DISTINCT_TOK LPAREN
      formula[f] { args.push_back(f); }
      ( COMMA formula[f] { args.push_back(f); } )* RPAREN
      {
        f = (args.size() == 1) ? SOLVER->mkTrue()
                               : MK_TERM(CVC4::api::DISTINCT, args);
      }
    )
    ( typeAscription[f, t]
      {
        f = PARSER_STATE->applyTypeAscription(f,t);
      }
    )?
  ;

relationTerm[CVC4::api::Term& f]
    /* relation terms */
  : TRANSPOSE_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::TRANSPOSE, f); }
  | TRANSCLOSURE_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::TCLOSURE, f); }
  | TUPLE_TOK LPAREN formula[f] RPAREN
    { std::vector<api::Sort> types;
      std::vector<api::Term> args;
      args.push_back(f);
      types.push_back(f.getSort());
      api::Sort t = SOLVER->mkTupleSort(types);
      const api::Datatype& dt = t.getDatatype();
      args.insert(args.begin(), dt[0].getConstructorTerm());
      f = MK_TERM(api::APPLY_CONSTRUCTOR, args);
    }
  | IDEN_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::IDEN, f); }
  | bvTerm[f]
  ;

bvTerm[CVC4::api::Term& f]
@init {
  api::Term f2;
  std::vector<api::Term> args;
}
    /* BV xor */
  : BVXOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_XOR, f, f2); }
  | BVNAND_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_NAND, f, f2); }
  | BVNOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_NOR, f, f2); }
  | BVCOMP_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_COMP, f, f2); }
  | BVXNOR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_XNOR, f, f2); }

    /* BV unary minus */
  | BVUMINUS_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_NEG, f); }
    /* BV addition */
  | BVPLUS_TOK LPAREN k=numeral COMMA formula[f] { args.push_back(f); }
    ( COMMA formula[f2] { args.push_back(f2); } )+ RPAREN
    {
      if (k <= 0) {
        PARSER_STATE->parseError("BVPLUS(k,_,_) must have k > 0");
      }
      for (unsigned i = 0; i < args.size(); ++ i) {
        ENSURE_BV_SIZE(k, args[i]);
      }
      f = MK_TERM(CVC4::api::BITVECTOR_PLUS, args);
    }
    /* BV subtraction */
  | BVSUB_TOK LPAREN k=numeral COMMA formula[f] COMMA formula[f2] RPAREN
    {
      if (k <= 0) {
        PARSER_STATE->parseError("BVSUB(k,_,_) must have k > 0");
      }
      ENSURE_BV_SIZE(k, f);
      ENSURE_BV_SIZE(k, f2);
      f = MK_TERM(CVC4::api::BITVECTOR_SUB, f, f2);
    }
    /* BV multiplication */
  | BVMULT_TOK LPAREN k=numeral COMMA formula[f] COMMA formula[f2] RPAREN
    {
      if (k <= 0) {
        PARSER_STATE->parseError("BVMULT(k,_,_) must have k > 0");
      }
      ENSURE_BV_SIZE(k, f);
      ENSURE_BV_SIZE(k, f2);
      f = MK_TERM(CVC4::api::BITVECTOR_MULT, f, f2);
    }
    /* BV unsigned division */
  | BVUDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_UDIV, f, f2); }
    /* BV signed division */
  | BVSDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SDIV, f, f2); }
    /* BV unsigned remainder */
  | BVUREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_UREM, f, f2); }
    /* BV signed remainder */
  | BVSREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SREM, f, f2); }
    /* BV signed modulo */
  | BVSMOD_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SMOD, f, f2); }
    /* BV left shift */
  | BVSHL_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SHL, f, f2); }
    /* BV arithmetic right shift */
  | BVASHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_ASHR, f, f2); }
    /* BV logical left shift */
  | BVLSHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_LSHR, f, f2); }
    /* BV sign extension */
  | SX_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { unsigned n = f.getSort().getBVSize();
      // Sign extension in TheoryBitVector is defined as in SMT-LIB
      // which is different than in the CVC language
      // SX(BITVECTOR(k), n) in CVC language extends to n bits
      // In SMT-LIB, such a thing expands to k + n bits
      f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_SIGN_EXTEND,k-n), f);
    }
    /* BV zero extension */
  | BVZEROEXTEND_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { unsigned n = f.getSort().getBVSize();
      // Zero extension in TheoryBitVector is defined as in SMT-LIB
      // which is the same as in CVC3, but different than SX!
      // SX(BITVECTOR(k), n) in CVC language extends to n bits
      // BVZEROEXTEND(BITVECTOR(k), n) in CVC language extends to k + n bits
      f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_ZERO_EXTEND,k), f);
    }
    /* BV repeat operation */
  | BVREPEAT_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_REPEAT,k), f); }
    /* BV rotate right */
  | BVROTR_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_ROTATE_RIGHT,k), f); }
    /* BV rotate left */
  | BVROTL_TOK LPAREN formula[f] COMMA k=numeral RPAREN
    { f = SOLVER->mkTerm(SOLVER->mkOp(api::BITVECTOR_ROTATE_LEFT,k), f); }

    /* BV comparisons */
  | BVLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_ULT, f, f2); }
  | BVLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_ULE, f, f2); }
  | BVGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_UGT, f, f2); }
  | BVGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_UGE, f, f2); }
  | BVSLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SLT, f, f2); }
  | BVSLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SLE, f, f2); }
  | BVSGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SGT, f, f2); }
  | BVSGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::BITVECTOR_SGE, f, f2); }
  | stringTerm[f]
  ;

stringTerm[CVC4::api::Term& f]
@init {
  api::Term f2;
  api::Term f3;
  std::string s;
  std::vector<api::Term> args;
}
    /* String prefix operators */
  : STRING_CONCAT_TOK LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f2] { args.push_back(f2); } )+ RPAREN
    { f = MK_TERM(CVC4::api::STRING_CONCAT, args); }
  | STRING_LENGTH_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_LENGTH, f); }
  | STRING_CONTAINS_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::STRING_CONTAINS, f, f2); }
  | STRING_SUBSTR_TOK LPAREN formula[f] COMMA formula[f2] COMMA formula[f3] RPAREN
    { f = MK_TERM(CVC4::api::STRING_SUBSTR, f, f2, f3); }
  | STRING_CHARAT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::STRING_CHARAT, f, f2); }
  | STRING_INDEXOF_TOK LPAREN formula[f] COMMA formula[f2] COMMA formula[f3] RPAREN
    { f = MK_TERM(CVC4::api::STRING_INDEXOF, f, f2, f3); }
  | STRING_REPLACE_TOK LPAREN formula[f] COMMA formula[f2] COMMA formula[f3] RPAREN
    { f = MK_TERM(CVC4::api::STRING_REPLACE, f, f2, f3); }
  | STRING_REPLACE_ALL_TOK LPAREN formula[f] COMMA formula[f2] COMMA formula[f3] RPAREN
    { f = MK_TERM(CVC4::api::STRING_REPLACE_ALL, f, f2, f3); }
  | STRING_PREFIXOF_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::STRING_PREFIX, f, f2); }
  | STRING_SUFFIXOF_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::STRING_SUFFIX, f, f2); }
  | STRING_STOI_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_TO_INT, f); }
  | STRING_ITOS_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_FROM_INT, f); }
  | STRING_TO_REGEXP_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_TO_REGEXP, f); }
  | STRING_TOLOWER_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_TOLOWER, f); }
  | STRING_TOUPPER_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_TOUPPER, f); }
  | STRING_REV_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::STRING_REV, f); }
  | REGEXP_CONCAT_TOK LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f2] { args.push_back(f2); } )+ RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_CONCAT, args); }
  | REGEXP_UNION_TOK LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f2] { args.push_back(f2); } )+ RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_UNION, args); }
  | REGEXP_INTER_TOK LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f2] { args.push_back(f2); } )+ RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_INTER, args); }
  | REGEXP_STAR_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_STAR, f); }
  | REGEXP_PLUS_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_PLUS, f); }
  | REGEXP_OPT_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_OPT, f); }
  | REGEXP_RANGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_RANGE, f, f2); }
  | REGEXP_LOOP_TOK LPAREN formula[f] COMMA lo=numeral COMMA hi=numeral RPAREN
    {
      api::Op lop = SOLVER->mkOp(CVC4::api::REGEXP_LOOP, lo, hi);
      f = MK_TERM(lop, f); 
    }
  | REGEXP_COMPLEMENT_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::REGEXP_COMPLEMENT, f); }
  | SEQ_UNIT_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::SEQ_UNIT, f); }
  | REGEXP_EMPTY_TOK
    { f = MK_TERM(CVC4::api::REGEXP_EMPTY, std::vector<api::Term>()); }
  | REGEXP_SIGMA_TOK
    { f = MK_TERM(CVC4::api::REGEXP_SIGMA, std::vector<api::Term>()); }

    /* string literal */
  | str[s]
    { f = PARSER_STATE->mkStringConstant(s); }

  | setsTerm[f]
  ;

setsTerm[CVC4::api::Term& f]
@init {
}
    /* Sets prefix operators */
  : SETS_CARD_TOK LPAREN formula[f] RPAREN
    { f = MK_TERM(CVC4::api::CARD, f); }
  | SETS_CHOOSE_TOK LPAREN formula[f] RPAREN
        { f = MK_TERM(CVC4::api::CHOOSE, f); }
  | simpleTerm[f]
  ;


/** Parses a simple term. */
simpleTerm[CVC4::api::Term& f]
@init {
  std::string name;
  std::vector<api::Term> args;
  std::vector<std::string> names;
  api::Term e;
  Debug("parser-extra") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
  api::Sort t, t2;
}
    /* if-then-else */
  : iteTerm[f]

    /* parenthesized sub-formula / tuple literals */
  | LPAREN formula[f] { args.push_back(f); }
    ( COMMA formula[f] { args.push_back(f); } )* RPAREN
    { if(args.size() > 1) {
        /* If args has elements, we must be a tuple literal.
         * Otherwise, f is already the sub-formula, and
         * there's nothing to do */
        std::vector<api::Sort> types;
        for (std::vector<api::Term>::const_iterator i = args.begin();
             i != args.end();
             ++i)
        {
          types.push_back((*i).getSort());
        }
        api::Sort dtype = SOLVER->mkTupleSort(types);
        const api::Datatype& dt = dtype.getDatatype();
        args.insert(args.begin(), dt[0].getConstructorTerm());
        f = MK_TERM(api::APPLY_CONSTRUCTOR, args);
      }
    }

    /* empty tuple literal */
  | LPAREN RPAREN
    { std::vector<api::Sort> types;
      api::Sort dtype = SOLVER->mkTupleSort(types);
      const api::Datatype& dt = dtype.getDatatype();
      f = MK_TERM(api::APPLY_CONSTRUCTOR, dt[0].getConstructorTerm());
    }

    /* empty record literal */
  | PARENHASH HASHPAREN
    {
      api::Sort dtype = SOLVER->mkRecordSort(
          std::vector<std::pair<std::string, api::Sort>>());
      const api::Datatype& dt = dtype.getDatatype();
      f = MK_TERM(api::APPLY_CONSTRUCTOR, dt[0].getConstructorTerm());
    }
    /* empty set literal */
  | LBRACE RBRACE
    { //boolean is placeholder
      f = SOLVER->mkEmptySet(SOLVER->mkSetSort(SOLVER->getBooleanSort()));
    }
  | UNIVSET_TOK
    { //boolean is placeholder
      f = SOLVER->mkUniverseSet(SOLVER->mkSetSort(SOLVER->getBooleanSort()));
    }

    /* finite set literal */
  | LBRACE formula[f] { args.push_back(f); }
    ( COMMA formula[f] { args.push_back(f); } )* RBRACE
    { f = MK_TERM(api::SINGLETON, args[0]);
      for(size_t i = 1; i < args.size(); ++i) {
        f = MK_TERM(api::UNION, f, MK_TERM(api::SINGLETON, args[i]));
      }
    }

    /* set cardinality literal */
  | BAR BAR formula[f] { args.push_back(f); } BAR BAR
    { f = MK_TERM(api::CARD, args[0]);
    }

    /* array literals */
  | ARRAY_TOK /* { PARSER_STATE->pushScope(); } */ LPAREN
    restrictedType[t, CHECK_DECLARED] OF_TOK restrictedType[t2, CHECK_DECLARED]
    RPAREN COLON simpleTerm[f]
    { /* Eventually if we support a bound var (like a lambda) for array
       * literals, we can use the push/pop scope. */
      /* PARSER_STATE->popScope(); */
      t = SOLVER->mkArraySort(t, t2);
      if(!f.isConst()) {
        std::stringstream ss;
        ss << "expected constant term inside array constant, but found "
           << "nonconstant term" << std::endl
           << "the term: " << f;
        PARSER_STATE->parseError(ss.str());
      }
      if(!t2.isComparableTo(f.getSort())) {
        std::stringstream ss;
        ss << "type mismatch inside array constant term:" << std::endl
           << "array type:          " << t << std::endl
           << "expected const type: " << t2 << std::endl
           << "computed const type: " << f.getSort();
        PARSER_STATE->parseError(ss.str());
      }
      f = SOLVER->mkConstArray(t, f);
    }

    /* boolean literals */
  | TRUE_TOK  { f = SOLVER->mkTrue(); }
  | FALSE_TOK { f = SOLVER->mkFalse(); }
    /* arithmetic literals */
    /* syntactic predicate: never match INTEGER.DIGIT as an integer and a dot!
     * This is a rational constant!  Otherwise the parser interprets it as a tuple
     * selector! */
  | DECIMAL_LITERAL {
      Rational r = AntlrInput::tokenToRational($DECIMAL_LITERAL);
      std::stringstream strRat;
      strRat << r;
      f = SOLVER->mkReal(strRat.str());
      if(f.getSort().isInteger()) {
        // Must cast to Real to ensure correct type is passed to parametric type constructors.
        // We do this cast using division with 1.
        // This has the advantage wrt using TO_REAL since (constant) division is always included in the theory.
        f = MK_TERM(api::DIVISION, f, SOLVER->mkReal(1));
      }
    }
  | INTEGER_LITERAL {
      Rational r = AntlrInput::tokenToRational($INTEGER_LITERAL);
      std::stringstream strRat;
      strRat << r;
      f = SOLVER->mkReal(strRat.str());
    }
    /* bitvector literals */
  | HEX_LITERAL
    { assert( AntlrInput::tokenText($HEX_LITERAL).find("0hex") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 4);
      f = SOLVER->mkBitVector(hexString, 16);
    }
  | BINARY_LITERAL
    { assert( AntlrInput::tokenText($BINARY_LITERAL).find("0bin") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 4);
      f = SOLVER->mkBitVector(binString, 2);
    }
    /* record literals */
  | PARENHASH recordEntry[name,e] { names.push_back(name); args.push_back(e); }
    ( COMMA recordEntry[name,e] { names.push_back(name); args.push_back(e); } )* HASHPAREN
    { std::vector< std::pair<std::string, api::Sort> > typeIds;
      assert(names.size() == args.size());
      for(unsigned i = 0; i < names.size(); ++i) {
        typeIds.push_back(std::make_pair(names[i], args[i].getSort()));
      }
      api::Sort dtype = SOLVER->mkRecordSort(typeIds);
      const api::Datatype& dt = dtype.getDatatype();
      args.insert(args.begin(), dt[0].getConstructorTerm());
      f = MK_TERM(api::APPLY_CONSTRUCTOR, args);
    }

    /* variable / zero-ary constructor application */
  | identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    /* ascriptions will be required for parameterized zero-ary constructors */
    { f = PARSER_STATE->getVariable(name);
      // datatypes: zero-ary constructors
      api::Sort dtype = f.getSort();
      if(dtype.isConstructor() && dtype.getConstructorArity() == 0) {
        // don't require parentheses, immediately turn it into an apply
        f = MK_TERM(CVC4::api::APPLY_CONSTRUCTOR, f);
      }
    }
  ;

/**
 * Matches a type ascription.
 * The f arg is the term to check (it is an input-only argument).
 */
typeAscription[const CVC4::api::Term& f, CVC4::api::Sort& t]
@init {
}
  : COLON COLON type[t,CHECK_DECLARED]
  ;

/**
 * Matches an entry in a record literal.
 */
recordEntry[std::string& name, CVC4::api::Term& ex]
  : identifier[name,CHECK_NONE,SYM_VARIABLE] ASSIGN_TOK formula[ex]
  ;

/**
 * Parses an ITE term.
 */
iteTerm[CVC4::api::Term& f]
@init {
  std::vector<api::Term> args;
  Debug("parser-extra") << "ite: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : IF_TOK formula[f] { args.push_back(f); }
    THEN_TOK formula[f] { args.push_back(f); }
    iteElseTerm[f] { args.push_back(f); }
    ENDIF_TOK
    { f = MK_TERM(CVC4::api::ITE, args); }
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseTerm[CVC4::api::Term& f]
@init {
  std::vector<api::Term> args;
  Debug("parser-extra") << "else: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : ELSE_TOK formula[f]
  | ELSEIF_TOK iteCondition = formula[f] { args.push_back(f); }
    THEN_TOK iteThen = formula[f] { args.push_back(f); }
    iteElse = iteElseTerm[f] { args.push_back(f); }
    { f = MK_TERM(CVC4::api::ITE, args); }
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[std::vector<CVC4::api::DatatypeDecl>& datatypes]
@init {
  std::string id, id2;
  api::Sort t;
  std::vector< api::Sort > params;
}
    /* This really needs to be CHECK_NONE, or mutually-recursive
     * datatypes won't work, because this type will already be
     * "defined" as an unresolved type; don't worry, we check
     * below. */
  : identifier[id,CHECK_NONE,SYM_SORT] { PARSER_STATE->pushScope(); }
    ( LBRACKET identifier[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2, ExprManager::SORT_FLAG_PLACEHOLDER);
        params.push_back( t );
      }
      ( COMMA identifier[id2,CHECK_UNDECLARED,SYM_SORT] {
        t = PARSER_STATE->mkSort(id2, ExprManager::SORT_FLAG_PLACEHOLDER);
        params.push_back( t ); }
      )* RBRACKET
    )?
    {
      datatypes.push_back(SOLVER->mkDatatypeDecl(id, params, false));
      if(!PARSER_STATE->isUnresolvedType(id)) {
        // if not unresolved, must be undeclared
        PARSER_STATE->checkDeclaration(id, CHECK_UNDECLARED, SYM_SORT);
      }
    }
    EQUAL_TOK constructorDef[datatypes.back()]
    ( BAR constructorDef[datatypes.back()] )*
    { PARSER_STATE->popScope(); }
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::api::DatatypeDecl& type]
@init {
  std::string id;
  std::unique_ptr<CVC4::api::DatatypeConstructorDecl> ctor;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT]
    {
      ctor.reset(new CVC4::api::DatatypeConstructorDecl(
          SOLVER->mkDatatypeConstructorDecl(id)));
    }
    ( LPAREN
      selector[&ctor]
      ( COMMA selector[&ctor] )*
      RPAREN
    )?
    { // make the constructor
      type.addConstructor(*ctor.get());
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
    }
  ;

selector[std::unique_ptr<CVC4::api::DatatypeConstructorDecl>* ctor]
@init {
  std::string id;
  api::Sort t, t2;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT] COLON type[t,CHECK_NONE]
    {
      (*ctor)->addSelector(id, t);
      Debug("parser-idt") << "selector: " << id.c_str() << std::endl;
    }
  ;

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER : (ALPHA | '_') (ALPHA | DIGIT | '_' | '\'' | '\\' | '?' | '$' | '~')*;

/**
 * Same as an integer literal converted to an unsigned int, but
 * slightly more convenient AND works around a strange ANTLR bug (?)
 * in the BVPLUS/BVMINUS/BVMULT rules where $INTEGER_LITERAL was
 * returning a reference to the wrong token?!
 */
numeral returns [unsigned k = 0]
  : INTEGER_LITERAL
    { $k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL); }
  ;

/**
 * Similar to numeral but for arbitrary-precision, signed integer.
 */
integer returns [CVC4::Rational k = 0]
  : INTEGER_LITERAL
    { $k = AntlrInput::tokenToInteger($INTEGER_LITERAL); }
  | MINUS_TOK INTEGER_LITERAL
    { $k = -AntlrInput::tokenToInteger($INTEGER_LITERAL); }
  ;

/**
 * Similar to numeral but for strings.
 */
str[std::string& s]
  : STRING_LITERAL
    { s = AntlrInput::tokenText($STRING_LITERAL);
      /* strip off the quotes */
      s = s.substr(1, s.size() - 2);
    }
  ;

/**
 * Matches a hexadecimal constant.
 */
HEX_LITERAL
  : '0hex' HEX_DIGIT+
  ;

/**
 * Matches a binary constant.
 */
BINARY_LITERAL
  : '0bin' ('0' | '1')+
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and
 * escape character '\' has to be escaped.
 */
STRING_LITERAL: '"' (ESCAPE | ~('"'|'\\'))* '"';

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment ALPHA : 'a'..'z' | 'A'..'Z';

/**
 * Matches the decimal digits (0-9)
 */
fragment DIGIT : '0'..'9';

// This rule adapted from http://www.antlr.org/wiki/pages/viewpage.action?pageId=13828121
// which reportedly comes from Tapestry (http://tapestry.apache.org/tapestry5/)
//
// Special rule that uses parsing tricks to identify numbers and ranges; it's all about
// the dot ('.').
// Recognizes:
// '.' as DOT
// '..' as DOTDOT
// INTEGER_LITERAL (digit+)
// DECIMAL_LITERAL (digit* . digit+)
// Has to watch out for embedded rangeop (i.e. "1..10" is not "1." and ".10").
//
// This doesn't ever generate the NUMBER_OR_RANGEOP token, it
// manipulates the $type inside to return the right token.
NUMBER_OR_RANGEOP
  : DIGIT+
    (
      { LA(2) != '.' }? => '.' DIGIT* { $type = DECIMAL_LITERAL; }
      | { $type = INTEGER_LITERAL; }
    )
  | '.'
    ( '.' {$type = DOTDOT; }
    | {$type = DOT; }
    )
  ;

// these empty fragments remove "no lexer rule corresponding to token" warnings
fragment INTEGER_LITERAL:;
fragment DECIMAL_LITERAL:;
fragment DOT:;
fragment DOTDOT:;

/**
 * Matches the hexadecimal digits (0-9, a-f, A-F)
 */
fragment HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';

/**
 * Matches and skips whitespace in the input and ignores it.
 */
WHITESPACE : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); };

/**
 * Matches the comments and ignores them
 */
COMMENT : '%' (~('\n' | '\r'))* { SKIP(); };

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');

/* *******************                                                        */
/*! \file Tptp.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Francois Bobot, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Parser for TPTP input language.
 **
 ** Parser for TPTP input language.
 ** cf. http://www.cs.miami.edu/~tptp/cgi-bin/SeeTPTP?Category=Documents&File=SyntaxBNF
 **/

grammar Tptp;

options {
  // C output for antlr
  language = 'C';

  // Skip the default error handling, just break with exceptions
  // defaultErrorHandler = false;

  // Only lookahead of <= k requested (disable for LL* parsing)
  // Note that CVC4's BoundedTokenBuffer requires a fixed k !
  // If you change this k, change it also in tptp_input.cpp !
  k = 2;
}/* options */

@header {
/**
 ** This file is part of CVC4.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}/* @header */

@lexer::includes {

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

/** This suppresses warnings about the redefinition of token symbols between
  * different parsers. The redefinitions should be harmless as long as no
  * client: (a) #include's the lexer headers for two grammars AND (b) uses the
  * token symbol definitions.
  */
#pragma GCC system_header

/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#define ANTLR3_INLINE_INPUT_ASCII

#include "parser/antlr_tracing.h"

}/* @lexer::includes */

@lexer::postinclude {
#include <stdint.h>

#include "parser/tptp/tptp.h"
#include "parser/antlr_input.h"

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Tptp*)LEXER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* @lexer::postinclude */

@parser::includes {

// This should come immediately after #include <antlr3.h> in the generated
// files. See the documentation in "parser/antlr_undefines.h" for more details.
#include "parser/antlr_undefines.h"

#include "smt/command.h"
#include "parser/parser.h"
#include "parser/tptp/tptp.h"
#include "parser/antlr_tracing.h"

}/* @parser::includes */

@parser::postinclude {

#include <algorithm>
#include <iterator>
#include <vector>

#include "base/output.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/tptp/tptp.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE
#define PARSER_STATE ((Tptp*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_EXPR_ASSOCIATIVE
#define MK_EXPR_ASSOCIATIVE EXPR_MANAGER->mkAssociative
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
#define UNSUPPORTED PARSER_STATE->unimplementedFeature

}/* parser::postinclude */

/**
 * Parses an expression.
 * @return the parsed expression, or the Null Expr if we've reached the end of the input
 */
parseExpr returns [CVC4::parser::tptp::myExpr expr]
  : cnfFormula[expr]
  | EOF
  ;

/**
 * Parses a command
 * @return the parsed command, or NULL if we've reached the end of the input
 */
parseCommand returns [CVC4::Command* cmd = NULL]
@declarations {
  Expr expr;
  Tptp::FormulaRole fr;
  std::string name, inclSymbol;
}
//  : LPAREN_TOK c = command RPAREN_TOK { $cmd = c; }
  : CNF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
  { PARSER_STATE->cnf = true; PARSER_STATE->fof = false; PARSER_STATE->pushScope(); }
    cnfFormula[expr]
  { PARSER_STATE->popScope();
    std::vector<Expr> bvl = PARSER_STATE->getFreeVar();
    if(!bvl.empty()) {
      expr = MK_EXPR(kind::FORALL,MK_EXPR(kind::BOUND_VAR_LIST,bvl),expr);
    };
  }
    (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      cmd = PARSER_STATE->makeCommand(fr, expr, /* cnf == */ true);
    }
  | FOF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
    { PARSER_STATE->cnf = false; PARSER_STATE->fof = true; }
    fofFormula[expr] (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      cmd = PARSER_STATE->makeCommand(fr, expr, /* cnf == */ false);
    }
  | TFF_TOK LPAREN_TOK nameN[name] COMMA_TOK
    ( TYPE_TOK COMMA_TOK tffTypedAtom[cmd]
    | formulaRole[fr] COMMA_TOK
      { PARSER_STATE->cnf = false; PARSER_STATE->fof = false; }
      tffFormula[expr] (COMMA_TOK anything*)?
      {
        cmd = PARSER_STATE->makeCommand(fr, expr, /* cnf == */ false);
      }
    ) RPAREN_TOK DOT_TOK
  | INCLUDE_TOK LPAREN_TOK unquotedFileName[name]
    ( COMMA_TOK LBRACK_TOK nameN[inclSymbol]
      ( COMMA_TOK nameN[inclSymbol] )* RBRACK_TOK )?
    RPAREN_TOK DOT_TOK
    { /* TODO - implement symbol filtering for file inclusion.
       * the following removes duplicates and "all", just need to pass it
       * through to includeFile() and implement it there.
      std::sort(inclArgs.begin(), inclArgs.end());
      std::vector<std::string>::iterator it =
        std::unique(inclArgs.begin(), inclArgs.end());
      inclArgs.resize(std::distance(inclArgs.begin(), it));
      it = std::lower_bound(inclArgs.begin(), inclArgs.end(), std::string("all"));
      if(it != inclArgs.end() && *it == "all") {
        inclArgs.erase(it);
      }
      */
      PARSER_STATE->includeFile(name /* , inclArgs */ );
      // The command of the included file will be produced at the next parseCommand() call
      cmd = new EmptyCommand("include::" + name);
    }
  | EOF
    {
      std::string filename = PARSER_STATE->getInput()->getInputStreamName();
      size_t i = filename.find_last_of('/');
      if(i != std::string::npos) {
        filename = filename.substr(i + 1);
      }
      if(filename.substr(filename.length() - 2) == ".p") {
        filename = filename.substr(0, filename.length() - 2);
      }
      CommandSequence* seq = new CommandSequence();
      seq->addCommand(new SetInfoCommand("name", SExpr(filename)));
      if(PARSER_STATE->hasConjecture()) {
        seq->addCommand(new QueryCommand(MK_CONST(bool(false))));
      } else {
        seq->addCommand(new CheckSatCommand());
      }
      PARSER_STATE->preemptCommand(seq);
      cmd = NULL;
    }
  ;

/* Parse a formula Role */
formulaRole[CVC4::parser::Tptp::FormulaRole& role]
  : LOWER_WORD
    {
      std::string r = AntlrInput::tokenText($LOWER_WORD);
      if      (r == "axiom")              role = Tptp::FR_AXIOM;
      else if (r == "hypothesis")         role = Tptp::FR_HYPOTHESIS;
      else if (r == "definition")         role = Tptp::FR_DEFINITION;
      else if (r == "assumption")         role = Tptp::FR_ASSUMPTION;
      else if (r == "lemma")              role = Tptp::FR_LEMMA;
      else if (r == "theorem")            role = Tptp::FR_THEOREM;
      else if (r == "negated_conjecture") role = Tptp::FR_NEGATED_CONJECTURE;
      else if (r == "conjecture")         role = Tptp::FR_CONJECTURE;
      else if (r == "unknown")            role = Tptp::FR_UNKNOWN;
      else if (r == "plain")              role = Tptp::FR_PLAIN;
      else if (r == "fi_domain")          role = Tptp::FR_FI_DOMAIN;
      else if (r == "fi_functor")         role = Tptp::FR_FI_FUNCTORS;
      else if (r == "fi_predicate")       role = Tptp::FR_FI_PREDICATES;
      else if (r == "type")               role = Tptp::FR_TYPE;
      else PARSER_STATE->parseError("Invalid formula role: " + r);
    }
  ;

/*******/
/* CNF */

/* It can parse a little more than the cnf grammar: false and true can appear.
 * Normally only false can appear and only at top level. */

cnfFormula[CVC4::Expr& expr]
  : LPAREN_TOK cnfDisjunction[expr] RPAREN_TOK
  | cnfDisjunction[expr]
//| FALSE_TOK { expr = MK_CONST(bool(false)); }
;

cnfDisjunction[CVC4::Expr& expr]
@declarations {
  std::vector<Expr> args;
}
  : cnfLiteral[expr] { args.push_back(expr); }
    ( OR_TOK cnfLiteral[expr] { args.push_back(expr); } )*
    { if(args.size() > 1) {
        expr = MK_EXPR_ASSOCIATIVE(kind::OR, args);
      } // else its already in the expr
    }
;

cnfLiteral[CVC4::Expr& expr]
  : atomicFormula[expr]
  | NOT_TOK atomicFormula[expr] { expr = MK_EXPR(kind::NOT, expr); }
//| folInfixUnary[expr]
  ;

atomicFormula[CVC4::Expr& expr]
@declarations {
  Expr expr2;
  std::string name;
  std::vector<CVC4::Expr> args;
  bool equal;
}
  : atomicWord[name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    ( equalOp[equal] term[expr2]
      { // equality/disequality between terms
        PARSER_STATE->makeApplication(expr, name, args, true);
        expr = MK_EXPR(kind::EQUAL, expr, expr2);
        if(!equal) expr = MK_EXPR(kind::NOT, expr);
      }
    | { // predicate
        PARSER_STATE->makeApplication(expr, name, args, false);
      }
    )
  | definedFun[expr] LPAREN_TOK arguments[args] RPAREN_TOK
    equalOp[equal] term[expr2]
    { expr = EXPR_MANAGER->mkExpr(expr, args);
      expr = MK_EXPR(kind::EQUAL, expr, expr2);
      if(!equal) expr = MK_EXPR(kind::NOT, expr);
    }
  | (simpleTerm[expr] | letTerm[expr] | conditionalTerm[expr])
    equalOp[equal] term[expr2]
    { // equality/disequality between terms
      expr = MK_EXPR(kind::EQUAL, expr, expr2);
      if(!equal) expr = MK_EXPR(kind::NOT, expr);
    }
  | definedPred[expr] LPAREN_TOK arguments[args] RPAREN_TOK
    { expr = EXPR_MANAGER->mkExpr(expr, args); }
  | definedProp[expr]
  ;
//%----Using <plain_term> removes a reduce/reduce ambiguity in lex/yacc.
//%----Note: "defined" means a word starting with one $ and "system" means $$.

definedProp[CVC4::Expr& expr]
  : TRUE_TOK { expr = MK_CONST(bool(true)); }
  | FALSE_TOK  { expr = MK_CONST(bool(false)); }
  ;

definedPred[CVC4::Expr& expr]
  : '$less' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::LT); }
  | '$lesseq' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::LEQ); }
  | '$greater' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::GT); }
  | '$greatereq' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::GEQ); }
  | '$is_rat' // all "real" are actually "rat" in CVC4
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      n = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n);
      expr = MK_EXPR(CVC4::kind::LAMBDA, n, MK_CONST(bool(true)));
    }
  | '$is_int' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::IS_INTEGER); }
  | '$distinct' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::DISTINCT); }
  ;

definedFun[CVC4::Expr& expr]
@declarations {
  bool remainder = false;
}
  : '$uminus' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::UMINUS); }
  | '$sum' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::PLUS); }
  | '$difference' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::MINUS); }
  | '$product' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::MULT); }
  | '$quotient' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::DIVISION_TOTAL); }
  | ( '$quotient_e' { remainder = false; }
    | '$remainder_e' { remainder = true; }
    )
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n, d);
      expr = MK_EXPR(CVC4::kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(CVC4::kind::ITE, MK_EXPR(CVC4::kind::GEQ, d, MK_CONST(Rational(0))),
                                      MK_EXPR(CVC4::kind::TO_INTEGER, expr),
                                      MK_EXPR(CVC4::kind::UMINUS, MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::UMINUS, expr))));
      if(remainder) {
        expr = MK_EXPR(CVC4::kind::MINUS, n, MK_EXPR(CVC4::kind::MULT, expr, d));
      }
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | ( '$quotient_t' { remainder = false; }
    | '$remainder_t' { remainder = true; }
    )
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n, d);
      expr = MK_EXPR(CVC4::kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(CVC4::kind::ITE, MK_EXPR(CVC4::kind::GEQ, expr, MK_CONST(Rational(0))),
                                      MK_EXPR(CVC4::kind::TO_INTEGER, expr),
                                      MK_EXPR(CVC4::kind::UMINUS, MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::UMINUS, expr))));
      if(remainder) {
        expr = MK_EXPR(CVC4::kind::MINUS, n, MK_EXPR(CVC4::kind::MULT, expr, d));
      }
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | ( '$quotient_f' { remainder = false; }
    | '$remainder_f' { remainder = true; }
    )
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n, d);
      expr = MK_EXPR(CVC4::kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(CVC4::kind::TO_INTEGER, expr);
      if(remainder) {
        expr = MK_EXPR(CVC4::kind::MINUS, n, MK_EXPR(CVC4::kind::MULT, expr, d));
      }
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | '$floor' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::TO_INTEGER); }
  | '$ceiling'
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n);
      expr = MK_EXPR(CVC4::kind::UMINUS, MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::UMINUS, n)));
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | '$truncate'
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n);
      expr = MK_EXPR(CVC4::kind::ITE, MK_EXPR(CVC4::kind::GEQ, n, MK_CONST(Rational(0))),
                                      MK_EXPR(CVC4::kind::TO_INTEGER, n),
                                      MK_EXPR(CVC4::kind::UMINUS, MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::UMINUS, n))));
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | '$round'
    { Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(CVC4::kind::BOUND_VAR_LIST, n);
      Expr decPart = MK_EXPR(CVC4::kind::MINUS, n, MK_EXPR(CVC4::kind::TO_INTEGER, n));
      expr = MK_EXPR(CVC4::kind::ITE, MK_EXPR(CVC4::kind::LT, decPart, MK_CONST(Rational(1, 2))),
                                      // if decPart < 0.5, round down
                                      MK_EXPR(CVC4::kind::TO_INTEGER, n),
             MK_EXPR(CVC4::kind::ITE, MK_EXPR(CVC4::kind::GT, decPart, MK_CONST(Rational(1, 2))),
                                      // if decPart > 0.5, round up
                                      MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::PLUS, n, MK_CONST(Rational(1)))),
                                      // if decPart == 0.5, round to nearest even integer:
                                      // result is: to_int(n/2 + .5) * 2
                                      MK_EXPR(CVC4::kind::MULT, MK_EXPR(CVC4::kind::TO_INTEGER, MK_EXPR(CVC4::kind::PLUS, MK_EXPR(CVC4::kind::DIVISION_TOTAL, n, MK_CONST(Rational(2))), MK_CONST(Rational(1, 2)))), MK_CONST(Rational(2)))));
      expr = MK_EXPR(CVC4::kind::LAMBDA, formals, expr);
    }
  | '$to_int' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::TO_INTEGER); }
  | '$to_rat' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::TO_REAL); }
  | '$to_real' { expr = EXPR_MANAGER->operatorOf(CVC4::kind::TO_REAL); }
  ;

//%----Pure CNF should not use $true or $false in problems, and use $false only
//%----at the roots of a refutation.

equalOp[bool& equal]
  : EQUAL_TOK    { equal = true; }
  | DISEQUAL_TOK { equal = false; }
  ;

term[CVC4::Expr& expr]
  : functionTerm[expr]
  | conditionalTerm[expr]
  | simpleTerm[expr]
  | letTerm[expr]
  ;

letTerm[CVC4::Expr& expr]
@declarations {
  CVC4::Expr lhs, rhs;
}
  : '$let_ft' LPAREN_TOK { PARSER_STATE->pushScope(); }
    tffLetFormulaDefn[lhs, rhs] COMMA_TOK
    term[expr]
    { PARSER_STATE->popScope();
      expr = expr.substitute(lhs, rhs);
    }
    RPAREN_TOK
  | '$let_tt' LPAREN_TOK { PARSER_STATE->pushScope(); }
    tffLetTermDefn[lhs, rhs] COMMA_TOK
    term[expr]
    { PARSER_STATE->popScope();
      expr = expr.substitute(lhs, rhs);
    }
    RPAREN_TOK
  ;

/* Not an application */
simpleTerm[CVC4::Expr& expr]
  : variable[expr]
  | NUMBER { expr = PARSER_STATE->d_tmp_expr; }
  | DISTINCT_OBJECT { expr = PARSER_STATE->convertStrToUnsorted(AntlrInput::tokenText($DISTINCT_OBJECT)); }
  ;

functionTerm[CVC4::Expr& expr]
@declarations {
  std::vector<CVC4::Expr> args;
}
  : plainTerm[expr]
  | definedFun[expr] LPAREN_TOK arguments[args] RPAREN_TOK
    { expr = EXPR_MANAGER->mkExpr(expr, args); }
// | <system_term>
  ;

conditionalTerm[CVC4::Expr& expr]
@declarations {
  CVC4::Expr expr2, expr3;
}
  : '$ite_t' LPAREN_TOK tffLogicFormula[expr] COMMA_TOK term[expr2] COMMA_TOK term[expr3] RPAREN_TOK
    { expr = EXPR_MANAGER->mkExpr(CVC4::kind::ITE, expr, expr2, expr3); }
  ;

plainTerm[CVC4::Expr& expr]
@declarations {
  std::string name;
  std::vector<Expr> args;
}
  : atomicWord[name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    {
       PARSER_STATE->makeApplication(expr,name,args,true);
    }
  ;

arguments[std::vector<CVC4::Expr>& args]
@declarations {
  Expr expr;
}
  :
  term[expr] { args.push_back(expr); } ( COMMA_TOK term[expr] { args.push_back(expr); } )*
  ;

variable[CVC4::Expr& expr]
  : UPPER_WORD
    {
      std::string name = AntlrInput::tokenText($UPPER_WORD);
      if(!PARSER_STATE->cnf || PARSER_STATE->isDeclared(name)) {
        expr = PARSER_STATE->getVariable(name);
      } else {
        expr = PARSER_STATE->mkBoundVar(name, PARSER_STATE->d_unsorted);
        if(PARSER_STATE->cnf) PARSER_STATE->addFreeVar(expr);
      }
    }
    ;

/*******/
/* FOF */
fofFormula[CVC4::Expr& expr] : fofLogicFormula[expr] ;

fofLogicFormula[CVC4::Expr& expr]
@declarations {
  tptp::NonAssoc na;
  std::vector< Expr > args;
  Expr expr2;
}
  : fofUnitaryFormula[expr]
    ( // Non-associative: <=> <~> ~& ~|
      ( fofBinaryNonAssoc[na] fofUnitaryFormula[expr2]
        { switch(na) {
           case tptp::NA_IFF:
             expr = MK_EXPR(kind::IFF,expr,expr2);
             break;
           case tptp::NA_REVIFF:
             expr = MK_EXPR(kind::XOR,expr,expr2);
             break;
           case tptp::NA_IMPLIES:
             expr = MK_EXPR(kind::IMPLIES,expr,expr2);
             break;
           case tptp::NA_REVIMPLIES:
             expr = MK_EXPR(kind::IMPLIES,expr2,expr);
             break;
           case tptp::NA_REVOR:
             expr = MK_EXPR(kind::NOT,MK_EXPR(kind::OR,expr,expr2));
             break;
           case tptp::NA_REVAND:
             expr = MK_EXPR(kind::NOT,MK_EXPR(kind::AND,expr,expr2));
             break;
          }
        }
      )
    | // N-ary and &
      ( { args.push_back(expr); }
        ( AND_TOK fofUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR_ASSOCIATIVE(kind::AND, args); }
      )
    | // N-ary or |
      ( { args.push_back(expr); }
        ( OR_TOK fofUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR_ASSOCIATIVE(kind::OR, args); }
      )
    )?
  ;

fofUnitaryFormula[CVC4::Expr& expr]
@declarations {
  Kind kind;
  std::vector< Expr > bv;
}
  : atomicFormula[expr]
  | LPAREN_TOK fofLogicFormula[expr] RPAREN_TOK
  | NOT_TOK fofUnitaryFormula[expr] { expr = MK_EXPR(kind::NOT,expr); }
  | // Quantified
    folQuantifier[kind] LBRACK_TOK {PARSER_STATE->pushScope();}
    ( bindvariable[expr] { bv.push_back(expr); }
      ( COMMA_TOK bindvariable[expr] { bv.push_back(expr); } )* ) RBRACK_TOK
    COLON_TOK fofUnitaryFormula[expr]
    { PARSER_STATE->popScope();
      expr = MK_EXPR(kind, MK_EXPR(kind::BOUND_VAR_LIST, bv), expr);
    }
  ;

bindvariable[CVC4::Expr& expr]
  : UPPER_WORD
    { std::string name = AntlrInput::tokenText($UPPER_WORD);
      expr = PARSER_STATE->mkBoundVar(name, PARSER_STATE->d_unsorted);
    }
  ;

fofBinaryNonAssoc[CVC4::parser::tptp::NonAssoc& na]
  : IFF_TOK      { na = tptp::NA_IFF; }
  | REVIFF_TOK   { na = tptp::NA_REVIFF; }
  | REVOR_TOK    { na = tptp::NA_REVOR; }
  | REVAND_TOK   { na = tptp::NA_REVAND; }
  | IMPLIES_TOK    { na = tptp::NA_IMPLIES; }
  | REVIMPLIES_TOK { na = tptp::NA_REVIMPLIES; }
  ;

folQuantifier[CVC4::Kind& kind]
  : BANG_TOK { kind = kind::FORALL; }
  | MARK_TOK { kind = kind::EXISTS; }
  ;

/*******/
/* TFF */
tffFormula[CVC4::Expr& expr] : tffLogicFormula[expr];

tffTypedAtom[CVC4::Command*& cmd]
@declarations {
  CVC4::Expr expr;
  CVC4::Type type;
  std::string name;
}
  : LPAREN_TOK tffTypedAtom[cmd] RPAREN_TOK
  | nameN[name] COLON_TOK
    ( '$tType'
      { if(PARSER_STATE->isDeclared(name, SYM_SORT)) {
          // duplicate declaration is fine, they're compatible
          cmd = new EmptyCommand("compatible redeclaration of sort " + name);
        } else if(PARSER_STATE->isDeclared(name, SYM_VARIABLE)) {
          // error: cannot be both sort and constant
          PARSER_STATE->parseError("Symbol `" + name + "' previously declared as a constant; cannot also be a sort");
        } else {
          // as yet, it's undeclared
          Type type = PARSER_STATE->mkSort(name);
          cmd = new DeclareTypeCommand(name, 0, type);
        }
      }
    | parseType[type]
      { if(PARSER_STATE->isDeclared(name, SYM_SORT)) {
          // error: cannot be both sort and constant
          PARSER_STATE->parseError("Symbol `" + name + "' previously declared as a sort");
          cmd = new EmptyCommand("compatible redeclaration of sort " + name);
        } else if(PARSER_STATE->isDeclared(name, SYM_VARIABLE)) {
          if(type == PARSER_STATE->getVariable(name).getType()) {
            // duplicate declaration is fine, they're compatible
            cmd = new EmptyCommand("compatible redeclaration of constant " + name);
          } else {
            // error: sorts incompatible
            PARSER_STATE->parseError("Symbol `" + name + "' declared previously with a different sort");
          }
        } else {
          // as yet, it's undeclared
          CVC4::Expr expr;
          if(type.isFunction()) {
            expr = PARSER_STATE->mkFunction(name, type);
          } else {
            expr = PARSER_STATE->mkVar(name, type);
          }
          cmd = new DeclareFunctionCommand(name, expr, type);
        }
      }
    )
  ;

tffLogicFormula[CVC4::Expr& expr]
@declarations {
  tptp::NonAssoc na;
  std::vector< Expr > args;
  Expr expr2;
}
  : tffUnitaryFormula[expr]
    ( // Non Assoc <=> <~> ~& ~|
      ( fofBinaryNonAssoc[na] tffUnitaryFormula[expr2]
        { switch(na) {
           case tptp::NA_IFF:
             expr = MK_EXPR(kind::IFF,expr,expr2);
             break;
           case tptp::NA_REVIFF:
             expr = MK_EXPR(kind::XOR,expr,expr2);
             break;
           case tptp::NA_IMPLIES:
             expr = MK_EXPR(kind::IMPLIES,expr,expr2);
             break;
           case tptp::NA_REVIMPLIES:
             expr = MK_EXPR(kind::IMPLIES,expr2,expr);
             break;
           case tptp::NA_REVOR:
             expr = MK_EXPR(kind::NOT,MK_EXPR(kind::OR,expr,expr2));
             break;
           case tptp::NA_REVAND:
             expr = MK_EXPR(kind::NOT,MK_EXPR(kind::AND,expr,expr2));
             break;
          }
        }
      )
    | // And &
      ( { args.push_back(expr); }
        ( AND_TOK tffUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR(kind::AND,args); }
      )
    | // Or |
      ( { args.push_back(expr); }
        ( OR_TOK tffUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR(kind::OR,args); }
      )
    )?
  ;

tffUnitaryFormula[CVC4::Expr& expr]
@declarations {
  Kind kind;
  std::vector< Expr > bv;
  Expr lhs, rhs;
}
  : atomicFormula[expr]
  | LPAREN_TOK tffLogicFormula[expr] RPAREN_TOK
  | NOT_TOK tffUnitaryFormula[expr] { expr = MK_EXPR(kind::NOT,expr); }
  | // Quantified
    folQuantifier[kind] LBRACK_TOK {PARSER_STATE->pushScope();}
    ( tffbindvariable[expr] { bv.push_back(expr); }
      ( COMMA_TOK tffbindvariable[expr] { bv.push_back(expr); } )* ) RBRACK_TOK
    COLON_TOK tffUnitaryFormula[expr]
    { PARSER_STATE->popScope();
      expr = MK_EXPR(kind, MK_EXPR(kind::BOUND_VAR_LIST, bv), expr);
    }
  | '$ite_f' LPAREN_TOK tffLogicFormula[expr] COMMA_TOK tffLogicFormula[lhs] COMMA_TOK tffLogicFormula[rhs] RPAREN_TOK
    { expr = EXPR_MANAGER->mkExpr(CVC4::kind::ITE, expr, lhs, rhs); }
  | '$let_tf' LPAREN_TOK { PARSER_STATE->pushScope(); }
    tffLetTermDefn[lhs, rhs] COMMA_TOK
    tffFormula[expr]
    { PARSER_STATE->popScope();
      expr = expr.substitute(lhs, rhs);
    }
    RPAREN_TOK
  | '$let_ff' LPAREN_TOK { PARSER_STATE->pushScope(); }
    tffLetFormulaDefn[lhs, rhs] COMMA_TOK
    tffFormula[expr]
    { PARSER_STATE->popScope();
      expr = expr.substitute(lhs, rhs);
    }
    RPAREN_TOK
  ;

tffLetTermDefn[CVC4::Expr& lhs, CVC4::Expr& rhs]
@declarations {
  std::vector<CVC4::Expr> bvlist;
}
  : (BANG_TOK LBRACK_TOK tffVariableList[bvlist] RBRACK_TOK COLON_TOK)*
    tffLetTermBinding[bvlist, lhs, rhs]
  ;

tffLetTermBinding[std::vector<CVC4::Expr>& bvlist, CVC4::Expr& lhs, CVC4::Expr& rhs]
  : term[lhs] EQUAL_TOK term[rhs]
    { PARSER_STATE->checkLetBinding(bvlist, lhs, rhs, false);
      rhs = MK_EXPR(CVC4::kind::LAMBDA, MK_EXPR(CVC4::kind::BOUND_VAR_LIST, lhs.getChildren()), rhs);
      lhs = lhs.getOperator();
    }
  | LPAREN_TOK tffLetTermBinding[bvlist, lhs, rhs] RPAREN_TOK
  ;

tffLetFormulaDefn[CVC4::Expr& lhs, CVC4::Expr& rhs]
@declarations {
  std::vector<CVC4::Expr> bvlist;
}
  : (BANG_TOK LBRACK_TOK tffVariableList[bvlist] RBRACK_TOK COLON_TOK)*
    tffLetFormulaBinding[bvlist, lhs, rhs]
  ;

tffLetFormulaBinding[std::vector<CVC4::Expr>& bvlist, CVC4::Expr& lhs, CVC4::Expr& rhs]
  : atomicFormula[lhs] IFF_TOK tffUnitaryFormula[rhs]
    { PARSER_STATE->checkLetBinding(bvlist, lhs, rhs, true);
      rhs = MK_EXPR(CVC4::kind::LAMBDA, MK_EXPR(CVC4::kind::BOUND_VAR_LIST, lhs.getChildren()), rhs);
      lhs = lhs.getOperator();
    }
  | LPAREN_TOK tffLetFormulaBinding[bvlist, lhs, rhs] RPAREN_TOK
  ;

tffbindvariable[CVC4::Expr& expr]
@declarations {
  CVC4::Type type = PARSER_STATE->d_unsorted;
}
  : UPPER_WORD
    ( COLON_TOK parseType[type] )?
    { std::string name = AntlrInput::tokenText($UPPER_WORD);
      expr = PARSER_STATE->mkBoundVar(name, type);
    }
  ;

// bvlist is accumulative; it can already contain elements
// on the way in, which are left undisturbed
tffVariableList[std::vector<CVC4::Expr>& bvlist]
@declarations {
  CVC4::Expr e;
}
  : tffbindvariable[e] { bvlist.push_back(e); }
    ( COMMA_TOK tffbindvariable[e] { bvlist.push_back(e); } )*
  ;

parseType[CVC4::Type& type]
@declarations {
  std::vector<CVC4::Type> v;
}
  : simpleType[type]
  | ( simpleType[type] { v.push_back(type); }
    | LPAREN_TOK simpleType[type] { v.push_back(type); }
      ( TIMES_TOK simpleType[type] { v.push_back(type); } )+
      RPAREN_TOK
    )
    GREATER_TOK simpleType[type]
    { v.push_back(type);
      type = EXPR_MANAGER->mkFunctionType(v);
    }
  ;

// non-function types
simpleType[CVC4::Type& type]
@declarations {
  std::string name;
}
  : DEFINED_SYMBOL
    { std::string s = AntlrInput::tokenText($DEFINED_SYMBOL);
      if(s == "\$i") type = PARSER_STATE->d_unsorted;
      else if(s == "\$o") type = EXPR_MANAGER->booleanType();
      else if(s == "\$int") type = EXPR_MANAGER->integerType();
      else if(s == "\$rat") type = EXPR_MANAGER->realType();
      else if(s == "\$real") type = EXPR_MANAGER->realType();
      else if(s == "\$tType") PARSER_STATE->parseError("Type of types `\$tType' cannot be used here");
      else PARSER_STATE->parseError("unknown defined type `" + s + "'");
    }
  | atomicWord[name]
    { type = PARSER_STATE->getSort(name); }
  ;

/***********************************************/
/* Anything well parenthesis */

anything
  : LPAREN_TOK anything* RPAREN_TOK
  | LBRACK_TOK anything* RBRACK_TOK
  | COMMA_TOK
  | DOT_TOK
  | COLON_TOK
  | OR_TOK
  | NOT_TOK
  | BANG_TOK
  | MARK_TOK
  | AND_TOK
  | IFF_TOK
  | IMPLIES_TOK
  | REVIMPLIES_TOK
  | REVIFF_TOK
  | REVOR_TOK
  | REVAND_TOK
  | TIMES_TOK
  | PLUS_TOK
  | MINUS_TOK
  | TRUE_TOK
  | FALSE_TOK
  | EQUAL_TOK
  | DISEQUAL_TOK
  | CNF_TOK
  | FOF_TOK
  | THF_TOK
  | TFF_TOK
  | TYPE_TOK
  | INCLUDE_TOK
  | DISTINCT_OBJECT
  | UPPER_WORD
  | LOWER_WORD
  | LOWER_WORD_SINGLE_QUOTED
  | SINGLE_QUOTED
  | NUMBER
  | DEFINED_SYMBOL
  ;
/*********/

//punctuation
COMMA_TOK  : ',';
DOT_TOK    : '.';
LPAREN_TOK : '(';
RPAREN_TOK : ')';
LBRACK_TOK : '[';
RBRACK_TOK : ']';
COLON_TOK  : ':';

GREATER_TOK  : '>';

//operator
OR_TOK       : '|';
NOT_TOK      : '~';
BANG_TOK     : '!';
MARK_TOK     : '?';
AND_TOK      : '&';
IFF_TOK      : '<=>';
IMPLIES_TOK    : '=>';
REVIMPLIES_TOK : '<=';
REVIFF_TOK   : '<~>';
REVOR_TOK    : '~|';
REVAND_TOK   : '~&';
TIMES_TOK    : '*';
PLUS_TOK     : '+';
MINUS_TOK    : '-';

//predicate
TRUE_TOK     : '$true';
FALSE_TOK    : '$false';
EQUAL_TOK    : '=';
DISEQUAL_TOK : '!=';

//KEYWORD
CNF_TOK     : 'cnf';
FOF_TOK     : 'fof';
THF_TOK     : 'thf';
TFF_TOK     : 'tff';
TYPE_TOK    : 'type';
INCLUDE_TOK : 'include';

//Other defined symbols, must be defined after all the other
DEFINED_SYMBOL : '$' LOWER_WORD;

/*********/
/* Token */

/*
 * Matches and skips whitespace in the input.
 */

WHITESPACE
  : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP(); }
  ;


/**
 * Matches a double or single quoted string literal. Escaping is supported, and
 * escape character '\' has to be escaped.
 */
DISTINCT_OBJECT : '"' (DO_CHAR)* '"' ;
fragment DO_CHAR : ' '..'!'| '#'..'[' | ']'..'~' | '\\"' | '\\\\';

//The order of this two rules is important
LOWER_WORD_SINGLE_QUOTED : '\'' LOWER_WORD '\'' ;
SINGLE_QUOTED : '\'' (SQ_CHAR)* '\'' ;

fragment SQ_CHAR : ' '..'&' | '('..'[' | ']'..'~' | '\\\'' | '\\\\';

/* Define upper (variable) and lower (everything else) word */
fragment NUMERIC : '0'..'9';
fragment LOWER_ALPHA : 'a'..'z';
fragment UPPER_ALPHA : 'A'..'Z';
fragment ALPHA_NUMERIC : LOWER_ALPHA | UPPER_ALPHA | NUMERIC | '_';
UPPER_WORD : UPPER_ALPHA ALPHA_NUMERIC*;
LOWER_WORD : LOWER_ALPHA ALPHA_NUMERIC*;

/* filename */
unquotedFileName[std::string& name] /* Beware fileName identifier is used by the backend ... */
 : (s=LOWER_WORD_SINGLE_QUOTED | s=SINGLE_QUOTED)
    { name = AntlrInput::tokenText($s);
      name = name.substr(1, name.size() - 2 );
    };

/* axiom name */
nameN[std::string& name]
 : atomicWord[name]
 | NUMBER { name = AntlrInput::tokenText($NUMBER); }
 ;

/* atomic word everything (fof, cnf, thf, tff, include must not be keyword at this position ) */
atomicWord[std::string& name]
 : FOF_TOK     { name = "fof"; }
 | CNF_TOK     { name = "cnf"; }
 | THF_TOK     { name = "thf"; }
 | TFF_TOK     { name = "tff"; }
 | TYPE_TOK    { name = "type"; }
 | INCLUDE_TOK { name = "include"; }
 | LOWER_WORD  { name = AntlrInput::tokenText($LOWER_WORD); }
 | LOWER_WORD_SINGLE_QUOTED // the lower word single quoted are considered without quote
    { /* strip off the quotes */
      name = AntlrInput::tokenTextSubstr($LOWER_WORD_SINGLE_QUOTED, 1 ,
                                         ($LOWER_WORD_SINGLE_QUOTED->stop - $LOWER_WORD_SINGLE_QUOTED->start) - 1);
    }
 | SINGLE_QUOTED {name = AntlrInput::tokenText($SINGLE_QUOTED); }; //for the others the quote remains

/** I don't understand how is made the difference between rational and real in SyntaxBNF. So I put all in rational */
/* Rational */

fragment DOT              : '.';
fragment EXPONENT         : 'E' | 'e';
fragment SLASH            : '/';

fragment DECIMAL : NUMERIC+;

/* Currently we put all in the rational type */
fragment SIGN[bool& pos]
  : PLUS_TOK { pos = true; }
  | MINUS_TOK { pos = false; }
  ;

NUMBER
@declarations {
  bool pos = true;
  bool posE = true;
}
  : ( SIGN[pos]? num=DECIMAL
      { Integer i(AntlrInput::tokenText($num));
        Rational r = pos ? i : -i;
        PARSER_STATE->d_tmp_expr = MK_CONST(r);
      }
    | SIGN[pos]? num=DECIMAL DOT den=DECIMAL (EXPONENT SIGN[posE]? e=DECIMAL)?
      { std::string snum = AntlrInput::tokenText($num);
        std::string sden = AntlrInput::tokenText($den);
        /* compute the numerator */
        Integer inum(snum + sden);
        // The sign
        inum = pos ? inum : -inum;
        // The exponent
        size_t exp = ($e == NULL ? 0 : AntlrInput::tokenToUnsigned($e));
        // Decimal part
        size_t dec = sden.size();
        /* multiply it by 10 raised to the exponent reduced by the
         * number of decimal place in den (dec) */
        Rational r;
        if(!posE) r = Rational(inum, Integer(10).pow(exp + dec));
        else if(exp == dec) r = Rational(inum);
        else if(exp > dec) r = Rational(inum * Integer(10).pow(exp - dec));
        else r = Rational(inum, Integer(10).pow(dec - exp));
        PARSER_STATE->d_tmp_expr = MK_CONST(r);
      }
    | SIGN[pos]? num=DECIMAL SLASH den=DECIMAL
      { Integer inum(AntlrInput::tokenText($num));
        Integer iden(AntlrInput::tokenText($den));
        PARSER_STATE->d_tmp_expr = MK_CONST(Rational(pos ? inum : -inum, iden));
      }
    )
    { if(PARSER_STATE->cnf || PARSER_STATE->fof) {
        // We're in an unsorted context, so put a conversion around it
        PARSER_STATE->d_tmp_expr = PARSER_STATE->convertRatToUnsorted( PARSER_STATE->d_tmp_expr );
      }
    }
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT
  : '%' (~('\n' | '\r'))*     { SKIP(); }     //comment line
  | '/*'  ( options {greedy=false;} : . )*  '*/' { SKIP(); } //comment block
  ;


/* *******************                                                        */
/*! \file Tptp.g
 ** \verbatim
 ** Top contributors (to current version):
 **   Francois Bobot, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.
 **/
}/* @header */

@lexer::includes {

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

#include <memory>

#include "smt/command.h"
#include "parser/parse_op.h"
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
  ParseOp p;
}
  : CNF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
  { PARSER_STATE->setCnf(true);
    PARSER_STATE->setFof(false);
    PARSER_STATE->pushScope(); }
    cnfFormula[expr]
  { PARSER_STATE->popScope();
    std::vector<Expr> bvl = PARSER_STATE->getFreeVar();
    if(!bvl.empty()) {
      expr = MK_EXPR(kind::FORALL,MK_EXPR(kind::BOUND_VAR_LIST,bvl),expr);
    };
  }
    (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      Expr aexpr = PARSER_STATE->getAssertionExpr(fr,expr);
      if( !aexpr.isNull() ){
        // set the expression name (e.g. used with unsat core printing)
        Command* csen = new SetExpressionNameCommand(aexpr, name);
        csen->setMuted(true);
        PARSER_STATE->preemptCommand(csen);
      }
      // make the command to assert the formula
      cmd = PARSER_STATE->makeAssertCommand(fr, aexpr, /* cnf == */ true, true);
    }
  | FOF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
    { PARSER_STATE->setCnf(false); PARSER_STATE->setFof(true); }
    fofFormula[expr] (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      Expr aexpr = PARSER_STATE->getAssertionExpr(fr,expr);
      if( !aexpr.isNull() ){
        // set the expression name (e.g. used with unsat core printing)
        Command* csen = new SetExpressionNameCommand(aexpr, name);
        csen->setMuted(true);
        PARSER_STATE->preemptCommand(csen);
      }
      // make the command to assert the formula
      cmd = PARSER_STATE->makeAssertCommand(fr, aexpr, /* cnf == */ false, true);
    }
  | TFF_TOK LPAREN_TOK nameN[name] COMMA_TOK
    ( TYPE_TOK COMMA_TOK tffTypedAtom[cmd]
    | formulaRole[fr] COMMA_TOK
      { PARSER_STATE->setCnf(false); PARSER_STATE->setFof(false); }
      tffFormula[expr] (COMMA_TOK anything*)?
      {
        Expr aexpr = PARSER_STATE->getAssertionExpr(fr,expr);
        if( !aexpr.isNull() ){
          // set the expression name (e.g. used with unsat core printing)
          Command* csen = new SetExpressionNameCommand(aexpr, name);
          csen->setMuted(true);
          PARSER_STATE->preemptCommand(csen);
        }
        // make the command to assert the formula
        cmd = PARSER_STATE->makeAssertCommand(fr, aexpr, /* cnf == */ false, true);
      }
    ) RPAREN_TOK DOT_TOK
  | THF_TOK LPAREN_TOK nameN[name] COMMA_TOK
    // Supported THF formulas: either a logic formula or a typing atom (i.e. we
    // ignore subtyping and logic sequents). Also, only TH0
    ( TYPE_TOK COMMA_TOK thfAtomTyping[cmd]
    | formulaRole[fr] COMMA_TOK
      { PARSER_STATE->setCnf(false); PARSER_STATE->setFof(false); }
      thfLogicFormula[p] (COMMA_TOK anything*)?
      {
        if (p.d_expr.isNull())
        {
          PARSER_STATE->parseError("Top level expression must be a formula");
        }
        expr = p.d_expr;
        Expr aexpr = PARSER_STATE->getAssertionExpr(fr, expr);
        if (!aexpr.isNull())
        {
          // set the expression name (e.g. used with unsat core printing)
          Command* csen = new SetExpressionNameCommand(aexpr, name);
          csen->setMuted(true);
          PARSER_STATE->preemptCommand(csen);
        }
        // make the command to assert the formula
        cmd = PARSER_STATE->makeAssertCommand(
            fr, aexpr, /* cnf == */ false, true);
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
      CommandSequence* seq = new CommandSequence();
      // assert that all distinct constants are distinct
      Expr aexpr = PARSER_STATE->getAssertionDistinctConstants();
      if( !aexpr.isNull() )
      {
        seq->addCommand(new AssertCommand(aexpr, false));
      }

      std::string filename = PARSER_STATE->getInput()->getInputStreamName();
      size_t i = filename.find_last_of('/');
      if(i != std::string::npos) {
        filename = filename.substr(i + 1);
      }
      if(filename.substr(filename.length() - 2) == ".p") {
        filename = filename.substr(0, filename.length() - 2);
      }
      seq->addCommand(new SetInfoCommand("filename", SExpr(filename)));
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
  ;

atomicFormula[CVC4::Expr& expr]
@declarations {
  Expr expr2;
  std::string name;
  std::vector<CVC4::Expr> args;
  bool equal;
  ParseOp p;
}
  : atomicWord[p.d_name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    ( equalOp[equal] term[expr2]
      { // equality/disequality between terms
        expr = args.empty() ? PARSER_STATE->parseOpToExpr(p)
                            : PARSER_STATE->applyParseOp(p, args);
        args.clear();
        args.push_back(expr);
        args.push_back(expr2);
        ParseOp p1(kind::EQUAL);
        expr = PARSER_STATE->applyParseOp(p1, args);
        if (!equal)
        {
          expr = MK_EXPR(kind::NOT, expr);
        }
      }
    | { // predicate
        p.d_type = EXPR_MANAGER->booleanType();
        expr = args.empty() ? PARSER_STATE->parseOpToExpr(p)
                            : PARSER_STATE->applyParseOp(p, args);
      }
    )
  | definedFun[p]
    (
     LPAREN_TOK arguments[args] RPAREN_TOK
     equalOp[equal] term[expr2]
     {
       expr = PARSER_STATE->applyParseOp(p, args);
       args.clear();
       args.push_back(expr);
       args.push_back(expr2);
       ParseOp p1(kind::EQUAL);
       expr = PARSER_STATE->applyParseOp(p1, args);
       if (!equal)
       {
         expr = MK_EXPR(kind::NOT, expr);
       }
     }
    )
  | (simpleTerm[expr] | letTerm[expr] | conditionalTerm[expr])
    (
      equalOp[equal] term[expr2]
      { // equality/disequality between terms
        args.push_back(expr);
        args.push_back(expr2);
        p.d_kind = kind::EQUAL;
        expr = PARSER_STATE->applyParseOp(p, args);
        if (!equal)
        {
          expr = MK_EXPR(kind::NOT, expr);
        }
      }
    )?
  | definedPred[p] (LPAREN_TOK arguments[args] RPAREN_TOK)
    {
      p.d_type = EXPR_MANAGER->booleanType();
      expr = PARSER_STATE->applyParseOp(p, args);
    }
  | definedProp[expr]
  ;

thfAtomicFormula[CVC4::ParseOp& p]
@declarations {
  Expr expr2;
  std::string name;
  std::vector<CVC4::Expr> args;
  bool equal;
}
  : atomicWord[p.d_name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    {
      p.d_expr = args.empty() ? PARSER_STATE->parseOpToExpr(p)
                              : PARSER_STATE->applyParseOp(p, args);
    }
  | definedFun[p]
    (
      LPAREN_TOK arguments[args] RPAREN_TOK
      equalOp[equal] term[expr2]
      {
        p.d_expr = PARSER_STATE->applyParseOp(p, args);
        args.clear();
        args.push_back(p.d_expr);
        args.push_back(expr2);
        ParseOp p1(kind::EQUAL);
        p.d_expr = PARSER_STATE->applyParseOp(p1, args);
        if (!equal)
        {
          p.d_expr = MK_EXPR(kind::NOT, p.d_expr);
        }
      }
    )?
  | thfSimpleTerm[p.d_expr]
  | letTerm[p.d_expr]
  | conditionalTerm[p.d_expr]
  | thfDefinedPred[p] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    {
      p.d_type = EXPR_MANAGER->booleanType();
      if (!args.empty())
      {
        p.d_expr = PARSER_STATE->applyParseOp(p, args);
      }
    }
  | definedProp[p.d_expr]
  ;

//%----Using <plain_term> removes a reduce/reduce ambiguity in lex/yacc.
//%----Note: "defined" means a word starting with one $ and "system" means $$.

definedProp[CVC4::Expr& expr]
  : TRUE_TOK { expr = MK_CONST(bool(true)); }
  | FALSE_TOK  { expr = MK_CONST(bool(false)); }
  ;

definedPred[CVC4::ParseOp& p]
  : '$less'
    {
      p.d_kind = kind::LT;
    }
  | '$lesseq'
    {
      p.d_kind = kind::LEQ;
    }
  | '$greater'
    {
      p.d_kind = kind::GT;
    }
  | '$greatereq'
    {
      p.d_kind = kind::GEQ;
    }
  | '$is_rat'
    // a real n is a rational if there exists q,r integers such that
    //   to_real(q) = n*to_real(r),
    // where r is non-zero.
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr q = EXPR_MANAGER->mkBoundVar("Q", EXPR_MANAGER->integerType());
      Expr qr = MK_EXPR(kind::TO_REAL, q);
      Expr r = EXPR_MANAGER->mkBoundVar("R", EXPR_MANAGER->integerType());
      Expr rr = MK_EXPR(kind::TO_REAL, r);
      Expr body =
          MK_EXPR(kind::AND,
                  MK_EXPR(kind::NOT,
                          MK_EXPR(kind::EQUAL, r, MK_CONST(Rational(0)))),
                  MK_EXPR(kind::EQUAL, qr, MK_EXPR(kind::MULT, n, rr)));
      Expr bvl = MK_EXPR(kind::BOUND_VAR_LIST, q, r);
      body = MK_EXPR(kind::EXISTS, bvl, body);
      Expr lbvl = MK_EXPR(kind::BOUND_VAR_LIST, n);
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, lbvl, body);
    }
  | '$is_int'
    {
      p.d_kind = kind::IS_INTEGER;
    }
  | '$distinct'
    {
      p.d_kind = kind::DISTINCT;
    }
  | AND_TOK
    {
      p.d_kind = kind::AND;
    }
  | IMPLIES_TOK
    {
      p.d_kind = kind::IMPLIES;
    }
  | OR_TOK
    {
      p.d_kind = kind::OR;
    }
  ;

thfDefinedPred[CVC4::ParseOp& p]
  : '$less'
     {
       p.d_kind = kind::LT;
     }
  | '$lesseq'
    {
      p.d_kind = kind::LEQ;
    }
  | '$greater'
    {
      p.d_kind = kind::GT;
    }
  | '$greatereq'
    {
      p.d_kind = kind::GEQ;
    }
  | '$is_rat'
    // a real n is a rational if there exists q,r integers such that
    //   to_real(q) = n*to_real(r),
    // where r is non-zero.
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr q = EXPR_MANAGER->mkBoundVar("Q", EXPR_MANAGER->integerType());
      Expr qr = MK_EXPR(kind::TO_REAL, q);
      Expr r = EXPR_MANAGER->mkBoundVar("R", EXPR_MANAGER->integerType());
      Expr rr = MK_EXPR(kind::TO_REAL, r);
      Expr body = MK_EXPR(
          kind::AND,
          MK_EXPR(kind::NOT,
                  MK_EXPR(kind::EQUAL, r, MK_CONST(Rational(0)))),
          MK_EXPR(kind::EQUAL, qr, MK_EXPR(kind::MULT, n, rr)));
      Expr bvl = MK_EXPR(kind::BOUND_VAR_LIST, q, r);
      body = MK_EXPR(kind::EXISTS, bvl, body);
      Expr lbvl = MK_EXPR(kind::BOUND_VAR_LIST, n);
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, lbvl, body);
    }
  | '$is_int'
    {
      p.d_kind = kind::IS_INTEGER;
    }
  | '$distinct'
    {
      p.d_kind = kind::DISTINCT;
    }
  | LPAREN_TOK
    (
      AND_TOK
      {
        p.d_kind = kind::AND;
      }
    | OR_TOK
      {
        p.d_kind = kind::OR;
      }
    | IMPLIES_TOK
      {
        p.d_kind = kind::IMPLIES;
      }
    )
    RPAREN_TOK
  ;

definedFun[CVC4::ParseOp& p]
@declarations {
  bool remainder = false;
}
  : '$uminus'
    {
      p.d_kind = kind::UMINUS;
    }
  | '$sum'
    {
      p.d_kind = kind::PLUS;
    }
  | '$difference'
    {
      p.d_kind = kind::MINUS;
    }
  | '$product'
    {
      p.d_kind = kind::MULT;
    }
  | '$quotient'
    {
      p.d_kind = kind::DIVISION;
    }
  | ( '$quotient_e' { remainder = false; }
    | '$remainder_e' { remainder = true; }
    )
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n, d);
      Expr expr = MK_EXPR(kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(kind::ITE,
                     MK_EXPR(kind::GEQ, d, MK_CONST(Rational(0))),
                     MK_EXPR(kind::TO_INTEGER, expr),
                     MK_EXPR(kind::UMINUS,
                             MK_EXPR(kind::TO_INTEGER,
                                     MK_EXPR(kind::UMINUS, expr))));
      if (remainder)
      {
        expr = MK_EXPR(
            kind::TO_INTEGER,
            MK_EXPR(kind::MINUS, n, MK_EXPR(kind::MULT, expr, d)));
      }
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
    }
  | ( '$quotient_t' { remainder = false; }
    | '$remainder_t' { remainder = true; }
    )
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n, d);
      Expr expr = MK_EXPR(kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(kind::ITE,
                     MK_EXPR(kind::GEQ, expr, MK_CONST(Rational(0))),
                     MK_EXPR(kind::TO_INTEGER, expr),
                     MK_EXPR(kind::UMINUS,
                             MK_EXPR(kind::TO_INTEGER,
                                     MK_EXPR(kind::UMINUS, expr))));
      if (remainder)
      {
        expr = MK_EXPR(
            kind::TO_INTEGER,
            MK_EXPR(kind::MINUS, n, MK_EXPR(kind::MULT, expr, d)));
      }
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
    }
  | ( '$quotient_f' { remainder = false; }
    | '$remainder_f' { remainder = true; }
    )
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr d = EXPR_MANAGER->mkBoundVar("D", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n, d);
      Expr expr = MK_EXPR(kind::DIVISION_TOTAL, n, d);
      expr = MK_EXPR(kind::TO_INTEGER, expr);
      if (remainder)
      {
        expr = MK_EXPR(kind::TO_INTEGER,
                       MK_EXPR(kind::MINUS, n, MK_EXPR(kind::MULT, expr, d)));
      }
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
    }
  | '$floor'
    {
      p.d_kind = kind::TO_INTEGER;
    }
  | '$ceiling'
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n);
      Expr expr = MK_EXPR(kind::UMINUS,
                          MK_EXPR(kind::TO_INTEGER, MK_EXPR(kind::UMINUS, n)));
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
    }
  | '$truncate'
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n);
      Expr expr =
          MK_EXPR(kind::ITE,
                  MK_EXPR(kind::GEQ, n, MK_CONST(Rational(0))),
                  MK_EXPR(kind::TO_INTEGER, n),
                  MK_EXPR(kind::UMINUS,
                          MK_EXPR(kind::TO_INTEGER, MK_EXPR(kind::UMINUS, n))));
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
    }
  | '$round'
    {
      Expr n = EXPR_MANAGER->mkBoundVar("N", EXPR_MANAGER->realType());
      Expr formals = MK_EXPR(kind::BOUND_VAR_LIST, n);
      Expr decPart = MK_EXPR(kind::MINUS, n, MK_EXPR(kind::TO_INTEGER, n));
      Expr expr = MK_EXPR(
          kind::ITE,
          MK_EXPR(kind::LT, decPart, MK_CONST(Rational(1, 2))),
          // if decPart < 0.5, round down
          MK_EXPR(kind::TO_INTEGER, n),
          MK_EXPR(kind::ITE,
                  MK_EXPR(kind::GT, decPart, MK_CONST(Rational(1, 2))),
                  // if decPart > 0.5, round up
                  MK_EXPR(kind::TO_INTEGER,
                          MK_EXPR(kind::PLUS, n, MK_CONST(Rational(1)))),
                  // if decPart == 0.5, round to nearest even integer:
                  // result is: to_int(n/2 + .5) * 2
                  MK_EXPR(kind::MULT,
                          MK_EXPR(kind::TO_INTEGER,
                                  MK_EXPR(kind::PLUS,
                                          MK_EXPR(kind::DIVISION_TOTAL,
                                                  n,
                                                  MK_CONST(Rational(2))),
                                          MK_CONST(Rational(1, 2)))),
                          MK_CONST(Rational(2)))));
      p.d_kind = kind::LAMBDA;
      p.d_expr = MK_EXPR(kind::LAMBDA, formals, expr);
      }
  | '$to_int'
    {
      p.d_kind = kind::TO_INTEGER;
    }
  | '$to_rat'
    {
      p.d_kind = kind::TO_REAL;
    }
  | '$to_real'
    {
      p.d_kind = kind::TO_REAL;
    }
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

/* Not an application */
thfSimpleTerm[CVC4::Expr& expr]
  : NUMBER { expr = PARSER_STATE->d_tmp_expr; }
  | DISTINCT_OBJECT
    {
      expr = PARSER_STATE->convertStrToUnsorted(
          AntlrInput::tokenText($DISTINCT_OBJECT));
    }
  ;

functionTerm[CVC4::Expr& expr]
@declarations {
  std::vector<CVC4::Expr> args;
  ParseOp p;
}
  : plainTerm[expr]
  | definedFun[p] LPAREN_TOK arguments[args] RPAREN_TOK
    {
      expr = PARSER_STATE->applyParseOp(p, args);
    }
  ;

conditionalTerm[CVC4::Expr& expr]
@declarations {
  CVC4::Expr expr2, expr3;
}
  : '$ite_t' LPAREN_TOK tffLogicFormula[expr] COMMA_TOK term[expr2] COMMA_TOK term[expr3] RPAREN_TOK
    { expr = EXPR_MANAGER->mkExpr(kind::ITE, expr, expr2, expr3); }
  ;

plainTerm[CVC4::Expr& expr]
@declarations {
  std::string name;
  std::vector<Expr> args;
  ParseOp p;
}
  : atomicWord[p.d_name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    {
      expr = args.empty() ? PARSER_STATE->parseOpToExpr(p)
                          : PARSER_STATE->applyParseOp(p, args);
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
      if(!PARSER_STATE->cnf() || PARSER_STATE->isDeclared(name)) {
        expr = PARSER_STATE->getVariable(name);
      } else {
        expr = PARSER_STATE->mkBoundVar(name, PARSER_STATE->d_unsorted);
        if(PARSER_STATE->cnf()) PARSER_STATE->addFreeVar(expr);
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
             expr = MK_EXPR(kind::EQUAL,expr,expr2);
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
  : FORALL_TOK { kind = kind::FORALL; }
  | EXISTS_TOK { kind = kind::EXISTS; }
  ;

/*******/
/* THF */

thfQuantifier[CVC4::Kind& kind]
  : FORALL_TOK { kind = kind::FORALL; }
  | EXISTS_TOK { kind = kind::EXISTS; }
  | LAMBDA_TOK { kind = kind::LAMBDA; }
  | CHOICE_TOK { kind = kind::CHOICE; }
  | DEF_DESC_TOK
    {
      UNSUPPORTED("Description quantifier");
    }
  | (TH1_UN_A | TH1_UN_E)
    {
      UNSUPPORTED("TH1 operator");
    }
  ;

thfAtomTyping[CVC4::Command*& cmd]
// for now only supports mapping types (i.e. no applied types)
@declarations {
  CVC4::Expr expr;
  CVC4::Type type;
  std::string name;
}
  : LPAREN_TOK thfAtomTyping[cmd] RPAREN_TOK
  | nameN[name] COLON_TOK
    ( '$tType'
      {
        if (PARSER_STATE->isDeclared(name, SYM_SORT))
        {
          // duplicate declaration is fine, they're compatible
          cmd = new EmptyCommand("compatible redeclaration of sort " + name);
        }
        else if (PARSER_STATE->isDeclared(name, SYM_VARIABLE))
        {
          // error: cannot be both sort and constant
          PARSER_STATE->parseError(
              "Symbol `" + name
              + "' previously declared as a constant; cannot also be a sort");
        }
        else
        {
          // as yet, it's undeclared
          Type type = PARSER_STATE->mkSort(name);
          cmd = new DeclareTypeCommand(name, 0, type);
        }
      }
    | parseThfType[type]
      {
        if (PARSER_STATE->isDeclared(name, SYM_SORT))
        {
          // error: cannot be both sort and constant
          PARSER_STATE->parseError("Symbol `" + name
                                   + "' previously declared as a sort");
          cmd = new EmptyCommand("compatible redeclaration of sort " + name);
        }
        else if (PARSER_STATE->isDeclared(name, SYM_VARIABLE))
        {
          if (type == PARSER_STATE->getVariable(name).getType())
          {
            // duplicate declaration is fine, they're compatible
            cmd = new EmptyCommand("compatible redeclaration of constant "
                                   + name);
          }
          else
          {
            // error: sorts incompatible
            PARSER_STATE->parseError(
                "Symbol `" + name
                + "' declared previously with a different sort");
          }
        }
        else
        {
          // as of yet, it's undeclared
          CVC4::Expr freshExpr;
          if (type.isFunction())
          {
            freshExpr = PARSER_STATE->mkVar(name, type);
          }
          else
          {
            freshExpr = PARSER_STATE->mkVar(name, type);
          }
          cmd = new DeclareFunctionCommand(name, freshExpr, type);
        }
      }
    )
  ;

thfLogicFormula[CVC4::ParseOp& p]
@declarations {
  tptp::NonAssoc na;
  std::vector<Expr> args;
  std::vector<ParseOp> p_args;
  Expr expr2;
  bool equal;
  ParseOp p1;
}
  //prefix unary formula case
  // ~
  : thfUnitaryFormula[p]
    ( // Equality: =
      equalOp[equal]
      thfUnitaryFormula[p1]
      {
        if (p.d_expr.isNull() && !p1.d_expr.isNull())
        {
          // make p.d_expr with a lambda of the same type as p1.d_expr
          p.d_expr =
              PARSER_STATE->mkLambdaWrapper(p.d_kind, p1.d_expr.getType());
        }
        else if (p1.d_expr.isNull() && !p.d_expr.isNull())
        {
          // make p1.d_expr with a lambda of the same type as p.d_expr
          p1.d_expr =
              PARSER_STATE->mkLambdaWrapper(p1.d_kind, p.d_expr.getType());
        }
        else if (p.d_expr.isNull() && p1.d_expr.isNull())
        {
          // Without a reference type it's not possible in general to know what
          // the lambda wrapping should be, so we fail in these cases
          UNSUPPORTED("Equality between theory functions");
        }
        args.push_back(p.d_expr);
        args.push_back(p1.d_expr);
        p.d_expr = MK_EXPR(kind::EQUAL, args);
        if (!equal)
        {
          p.d_expr = MK_EXPR(kind::NOT, p.d_expr);
        }
      }
    | // Non-associative: <=> <~> ~& ~|
      fofBinaryNonAssoc[na] thfUnitaryFormula[p1]
      {
        if (p.d_expr.isNull() || p1.d_expr.isNull())
        {
          PARSER_STATE->parseError(
              "Non-associative operator must be applied to formulas");
        }
        switch (na)
        {
          case tptp::NA_IFF:
            p.d_expr = MK_EXPR(kind::EQUAL, p.d_expr, p1.d_expr);
            break;
          case tptp::NA_REVIFF:
            p.d_expr = MK_EXPR(kind::XOR, p.d_expr, p1.d_expr);
            break;
          case tptp::NA_IMPLIES:
            p.d_expr = MK_EXPR(kind::IMPLIES, p.d_expr, p1.d_expr);
            break;
          case tptp::NA_REVIMPLIES:
            p.d_expr = MK_EXPR(kind::IMPLIES, p1.d_expr, p.d_expr);
            break;
          case tptp::NA_REVOR:
            p.d_expr =
                MK_EXPR(kind::NOT, MK_EXPR(kind::OR, p.d_expr, p1.d_expr));
            break;
          case tptp::NA_REVAND:
            p.d_expr =
                MK_EXPR(kind::NOT, MK_EXPR(kind::AND, p.d_expr, p1.d_expr));
            break;
        }
      }
    | // N-ary and &
      (
        {
          if (p.d_expr.isNull())
          {
            PARSER_STATE->parseError("AND must be applied to a formula");
          }
          args.push_back(p.d_expr);
          p = ParseOp();
        }
        ( AND_TOK thfUnitaryFormula[p]
          {
            if (p.d_expr.isNull())
            {
              PARSER_STATE->parseError("AND must be applied to a formula");
            }
            args.push_back(p.d_expr);
            p = ParseOp();
          }
        )+
        {
          p.d_expr = MK_EXPR_ASSOCIATIVE(kind::AND, args);
        }
      )
    | // N-ary or |
      (
        {
          if (p.d_expr.isNull())
          {
            PARSER_STATE->parseError("OR must be applied to a formula");
          }
          args.push_back(p.d_expr);
          p = ParseOp();
        }
        ( OR_TOK thfUnitaryFormula[p]
          {
            if (p.d_expr.isNull())
            {
              PARSER_STATE->parseError("OR must be applied to a formula");
            }
            args.push_back(p.d_expr);
            p = ParseOp();
          }
        )+
        {
          p.d_expr = MK_EXPR_ASSOCIATIVE(kind::OR, args);
        }
      )
    | // N-ary @ |
      //
      // @ (denoting apply) is left-associative and lambda is right-associative.
      // ^ [X] : ^ [Y] : f @ g (where f is a <thf_apply_formula> and g is a
      // <thf_unitary_formula>) should be parsed as: (^ [X] : (^ [Y] : f)) @ g.
      // That is, g is not in the scope of either lambda.
      {
        p_args.push_back(p);
        p = ParseOp();
      }
      ( APP_TOK
        (
         thfUnitaryFormula[p]
         {
           p_args.push_back(p);
           p = ParseOp();
         }
         | LBRACK_TOK
           { UNSUPPORTED("Tuple terms"); }
           thfTupleForm[args]
           RBRACK_TOK
        )
      )+
      {
        if (p_args[0].d_expr.isNull())
        {
          for (unsigned i = 1, size = p_args.size(); i < size; ++i)
          {
            if (p_args[i].d_expr.isNull())
            {
              PARSER_STATE->parseError(
                  "Application chains with defined symbol heads and at least "
                  "one defined symbol as argument are unsupported.");
            }
            args.push_back(p_args[i].d_expr);
          }
          p.d_expr = PARSER_STATE->applyParseOp(p_args[0], args);
        }
        else
        {
          p.d_expr = p_args[0].d_expr;
          // check if any argument is a defined function, e.g. "~", and create a
          // lambda wrapper then, e.g. (\lambda x. ~ x)
          for (unsigned i = 1, size = p_args.size(); i < size; ++i)
          {
            if (!p_args[i].d_expr.isNull())
            {
              args.push_back(p_args[i].d_expr);
              continue;
            }
            // create a lambda wrapper, e.g. (\lambda x. ~ x).
            //
            // The type is determined by the first element of the application
            // chain, which must be a function of type t1...tn -> t, so the
            // lambda must have type ti
            args.push_back(PARSER_STATE->mkLambdaWrapper(
                p_args[i].d_kind,
                (static_cast<FunctionType>(p.d_expr.getType()))
                    .getArgTypes()[i - 1]));
          }
          for (unsigned i = 0, size = args.size(); i < size; ++i)
          {
            p.d_expr = MK_EXPR(kind::HO_APPLY, p.d_expr, args[i]);
          }
        }
      }
    )?
  ;

thfTupleForm[std::vector<CVC4::Expr>& args]
@declarations {
  ParseOp p;
}
  : thfUnitaryFormula[p]
   {
     if (p.d_expr.isNull())
     {
       PARSER_STATE->parseError("TUPLE element must be a formula");
     }
     args.push_back(p.d_expr);
   }
   ( COMMA_TOK thfUnitaryFormula[p]
     {
       if (p.d_expr.isNull())
       {
         PARSER_STATE->parseError("TUPLE element must be a formula");
       }
       args.push_back(p.d_expr);
     }
   )+
;

thfUnitaryFormula[CVC4::ParseOp& p]
@declarations {
  Kind kind;
  std::vector< Expr > bv;
  Expr expr;
  bool equal;
  ParseOp p1;
}
  : variable[p.d_expr]
  | thfAtomicFormula[p]
  | LPAREN_TOK
    thfLogicFormula[p]
    RPAREN_TOK
  | NOT_TOK
    {
      p.d_kind = kind::NOT;
    }
    (
     thfUnitaryFormula[p1]
     {
       if (p1.d_expr.isNull())
       {
         PARSER_STATE->parseError("NOT must be applied to a formula");
       }
       std::vector<Expr> args{p1.d_expr};
       p.d_expr = PARSER_STATE->applyParseOp(p, args);
     }
    )?
  | // Quantified
    thfQuantifier[p.d_kind]
    LBRACK_TOK {PARSER_STATE->pushScope();}
    thfBindVariable[expr]
    {
      bv.push_back(expr);
    }
    ( COMMA_TOK thfBindVariable[expr]
      {
        bv.push_back(expr);
      }
    )*
    RBRACK_TOK COLON_TOK
    thfUnitaryFormula[p1]
    {
      if (p1.d_expr.isNull())
      {
        PARSER_STATE->parseError("In scope of binder there must be a formula.");
      }
      expr = p1.d_expr;
      PARSER_STATE->popScope();
      // handle lambda case, in which case return type must be flattened and the
      // auxiliary variables introduced in the proccess must be added no the
      // variable list
      //
      // see documentation of mkFlatFunctionType for how it's done
      //
      // flatten body via flattening its type
      std::vector<Type> sorts;
      std::vector<Expr> flattenVars;
      PARSER_STATE->mkFlatFunctionType(sorts, expr.getType(), flattenVars);
      if (!flattenVars.empty())
      {
        // apply body of lambda to flatten vars
        expr = PARSER_STATE->mkHoApply(expr, flattenVars);
        // add variables to BOUND_VAR_LIST
        bv.insert(bv.end(), flattenVars.begin(), flattenVars.end());
      }
      p.d_expr = MK_EXPR(p.d_kind, MK_EXPR(kind::BOUND_VAR_LIST, bv), expr);
    }
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
          CVC4::Expr expr = PARSER_STATE->mkVar(name, type);
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
             expr = MK_EXPR(kind::EQUAL,expr,expr2);
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
    { expr = EXPR_MANAGER->mkExpr(kind::ITE, expr, lhs, rhs); }
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
  : (FORALL_TOK LBRACK_TOK tffVariableList[bvlist] RBRACK_TOK COLON_TOK)*
    tffLetTermBinding[bvlist, lhs, rhs]
  ;

tffLetTermBinding[std::vector<CVC4::Expr>& bvlist, CVC4::Expr& lhs, CVC4::Expr& rhs]
  : term[lhs] EQUAL_TOK term[rhs]
    { PARSER_STATE->checkLetBinding(bvlist, lhs, rhs, false);
      rhs = MK_EXPR(kind::LAMBDA, MK_EXPR(kind::BOUND_VAR_LIST, lhs.getChildren()), rhs);
      lhs = lhs.getOperator();
    }
  | LPAREN_TOK tffLetTermBinding[bvlist, lhs, rhs] RPAREN_TOK
  ;

tffLetFormulaDefn[CVC4::Expr& lhs, CVC4::Expr& rhs]
@declarations {
  std::vector<CVC4::Expr> bvlist;
}
  : (FORALL_TOK LBRACK_TOK tffVariableList[bvlist] RBRACK_TOK COLON_TOK)*
    tffLetFormulaBinding[bvlist, lhs, rhs]
  ;

tffLetFormulaBinding[std::vector<CVC4::Expr>& bvlist, CVC4::Expr& lhs, CVC4::Expr& rhs]
  : atomicFormula[lhs] IFF_TOK tffUnitaryFormula[rhs]
    { PARSER_STATE->checkLetBinding(bvlist, lhs, rhs, true);
      rhs = MK_EXPR(kind::LAMBDA, MK_EXPR(kind::BOUND_VAR_LIST, lhs.getChildren()), rhs);
      lhs = lhs.getOperator();
    }
  | LPAREN_TOK tffLetFormulaBinding[bvlist, lhs, rhs] RPAREN_TOK
  ;

thfBindVariable[CVC4::Expr& expr]
@declarations {
  std::string name;
  CVC4::Type type = PARSER_STATE->d_unsorted;
}
  : UPPER_WORD
    { name = AntlrInput::tokenText($UPPER_WORD); }
    ( COLON_TOK parseThfType[type] )?
    {
      expr = PARSER_STATE->mkBoundVar(name, type);
    }
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

parseThfType[CVC4::Type& type]
// assumes only mapping types (arrows), no tuple type
@declarations {
  std::vector<CVC4::Type> sorts;
}
  : thfType[type] { sorts.push_back(type); }
    (
     (ARROW_TOK | TIMES_TOK) thfType[type] { sorts.push_back(type); }
    )*
    {
      if (sorts.size() < 1)
      {
        type = sorts[0];
      }
      else
      {
        Type range = sorts.back();
        sorts.pop_back();
        type = PARSER_STATE->mkFlatFunctionType(sorts, range);
      }
    }
  ;

thfType[CVC4::Type& type]
// assumes only mapping types (arrows), no tuple type
  : simpleType[type]
    | LPAREN_TOK parseThfType[type] RPAREN_TOK
    | LBRACK_TOK { UNSUPPORTED("Tuple types"); } parseThfType[type] RBRACK_TOK
  ;

parseType[CVC4::Type & type]
@declarations
{
  std::vector<CVC4::Type> v;
}
  : simpleType[type]
  | ( simpleType[type] { v.push_back(type); }
    | LPAREN_TOK simpleType[type] { v.push_back(type); }
      ( TIMES_TOK simpleType[type] { v.push_back(type); } )+
      RPAREN_TOK
    )
    ARROW_TOK simpleType[type]
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
  | FORALL_TOK
  | EXISTS_TOK
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

// typing
ARROW_TOK   : '>';
SUBTYPE_TOK : '>>';

//operator
OR_TOK         : '|';
NOT_TOK        : '~';
FORALL_TOK     : '!';
EXISTS_TOK     : '?';
LAMBDA_TOK     : '^';
CHOICE_TOK     : '@+';
DEF_DESC_TOK   : '@-';
AND_TOK        : '&';
IFF_TOK        : '<=>';
IMPLIES_TOK    : '=>';
REVIMPLIES_TOK : '<=';
REVIFF_TOK     : '<~>';
REVOR_TOK      : '~|';
REVAND_TOK     : '~&';
TIMES_TOK      : '*';
PLUS_TOK       : '+';
MINUS_TOK      : '-';
APP_TOK        : '@';

TH1_UN_A       : '!!';
TH1_UN_E       : '??';

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
    { if(PARSER_STATE->cnf() || PARSER_STATE->fof()) {
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

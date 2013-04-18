/* *******************                                                        */
/*! \file Tptp.g
 ** \verbatim
 ** Original author: Francois Bobot
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
  k = 1;
}/* options */

@header {
/**
 ** This file is part of CVC4.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
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
#include "expr/command.h"
#include "parser/parser.h"
#include "parser/tptp/tptp.h"
#include "parser/antlr_tracing.h"

}/* @parser::includes */

@parser::postinclude {

#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "parser/tptp/tptp.h"
#include "util/integer.h"
#include "util/output.h"
#include "util/rational.h"
#include <vector>

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
  std::string name;
  std::string incl_args;
}
//  : LPAREN_TOK c = command RPAREN_TOK { $cmd = c; }
  : CNF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
  { PARSER_STATE->cnf=true; PARSER_STATE->pushScope(); }
    cnfFormula[expr]
  { PARSER_STATE->popScope();
    std::vector<Expr> bvl = PARSER_STATE->getFreeVar();
    if(!bvl.empty()){
      expr = MK_EXPR(kind::FORALL,MK_EXPR(kind::BOUND_VAR_LIST,bvl),expr);
    };
  }
    (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      cmd = PARSER_STATE->makeCommand(fr,expr);
    }
  | FOF_TOK LPAREN_TOK nameN[name] COMMA_TOK formulaRole[fr] COMMA_TOK
    { PARSER_STATE->cnf=false; }
    fofFormula[expr] (COMMA_TOK anything*)? RPAREN_TOK DOT_TOK
    {
      cmd = PARSER_STATE->makeCommand(fr,expr);
    }
  | INCLUDE_TOK LPAREN_TOK unquotedFileName[name]
    ( COMMA_TOK LBRACK_TOK nameN[incl_args] ( COMMA_TOK nameN[incl_args] )* RBRACK_TOK )?
    RPAREN_TOK DOT_TOK
    {
      PARSER_STATE->includeFile(name);
      // The command of the included file will be produce at the new parseCommand call
      cmd = new EmptyCommand("include::" + name);
    }
  | EOF
    {
      PARSER_STATE->preemptCommand(new CheckSatCommand(MK_CONST(bool(true))));
      cmd = NULL;
    }
  ;

/* Parse a formula Role */
formulaRole[CVC4::parser::Tptp::FormulaRole & role]
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
   Normally only false can appear and only at top level
*/

cnfFormula[CVC4::Expr& expr]
  :
  LPAREN_TOK disjunction[expr] RPAREN_TOK
| disjunction[expr]
//| FALSE_TOK { expr = MK_CONST(bool(false)); }
;

disjunction[CVC4::Expr& expr]
@declarations {
  std::vector<Expr> args;
}
  :
    literal[expr] {args.push_back(expr); } ( OR_TOK literal[expr] {args.push_back(expr); } )*
    {
      if(args.size() > 1){
        expr = MK_EXPR(kind::OR,args);
      } // else its already in the expr
    }
;

literal[CVC4::Expr& expr]
  : atomicFormula[expr]
  | NOT_TOK atomicFormula[expr] { expr = MK_EXPR(kind::NOT,expr); }
//  | folInfixUnary[expr]
  ;

atomicFormula[CVC4::Expr& expr]
@declarations {
  Expr expr2;
  std::string name;
  std::vector<CVC4::Expr> args;
  bool equal;
}
  : atomicWord[name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    ( ( equalOp[equal] //equality/disequality between terms
       {
         PARSER_STATE->makeApplication(expr,name,args,true);
       }
       term[expr2]
       {
         expr = MK_EXPR(kind::EQUAL, expr, expr2);
         if(!equal) expr = MK_EXPR(kind::NOT,expr);
       }
      )
    | //predicate
      {
        PARSER_STATE->makeApplication(expr,name,args,false);
      }
  )
  | simpleTerm[expr] equalOp[equal] term[expr2]
    {
      expr = MK_EXPR(kind::EQUAL, expr, expr2);
      if(!equal) expr = MK_EXPR(kind::NOT,expr);
    }
  | definedProp[expr]
;
//%----Using <plain_term> removes a reduce/reduce ambiguity in lex/yacc.
//%----Note: "defined" means a word starting with one $ and "system" means $$.

definedProp[CVC4::Expr& expr]
  : TRUE_TOK { expr = MK_CONST(bool(true)); }
  | FALSE_TOK  { expr = MK_CONST(bool(false)); }
  ;
//%----Pure CNF should not use $true or $false in problems, and use $false only
//%----at the roots of a refutation.

equalOp[bool & equal]
 :  EQUAL_TOK    {equal = true;}
  | DISEQUAL_TOK {equal = false;}
  ;

term[CVC4::Expr& expr]
 : functionTerm[expr]
  | simpleTerm[expr]
//  | conditionalTerm
//  | let_term
  ;

/* Not an application */
simpleTerm[CVC4::Expr& expr]
  : variable[expr]
  | NUMBER { expr = PARSER_STATE->d_tmp_expr; }
  | DISTINCT_OBJECT { expr = PARSER_STATE->convertStrToUnsorted(
        AntlrInput::tokenText($DISTINCT_OBJECT)); }
;

functionTerm[CVC4::Expr& expr]
  : plainTerm[expr] // | <defined_term> | <system_term>
  ;

plainTerm[CVC4::Expr& expr]
@declarations{
  std::string name;
  std::vector<Expr> args;
}
  : atomicWord[name] (LPAREN_TOK arguments[args] RPAREN_TOK)?
    {
       PARSER_STATE->makeApplication(expr,name,args,true);
    }
  ;

arguments[std::vector<CVC4::Expr> & args]
@declarations{
  Expr expr;
}
  :
  term[expr] { args.push_back(expr); } ( COMMA_TOK term[expr] { args.push_back(expr); } )*
  ;

variable[CVC4::Expr & expr]
  : UPPER_WORD
    {
      std::string name = AntlrInput::tokenText($UPPER_WORD);
      if(!PARSER_STATE->cnf || PARSER_STATE->isDeclared(name)){
        expr = PARSER_STATE->getVariable(name);
      } else {
        expr = PARSER_STATE->mkBoundVar(name, PARSER_STATE->d_unsorted);
        if(PARSER_STATE->cnf) PARSER_STATE->addFreeVar(expr);
      }
    }
    ;

/*******/
/* FOF */
fofFormula[CVC4::Expr & expr] : fofLogicFormula[expr] ;

fofLogicFormula[CVC4::Expr & expr]
@declarations{
  tptp::NonAssoc na;
  std::vector< Expr > args;
  Expr expr2;
}
  : fofUnitaryFormula[expr]
    ( //Non Assoc <=> <~> ~& ~|
      ( fofBinaryNonAssoc[na] fofUnitaryFormula[expr2]
        { switch(na){
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
    | //And &
      ( { args.push_back(expr); }
        ( AND_TOK fofUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR(kind::AND,args); }
      )
    | //Or |
      ( { args.push_back(expr); }
        ( OR_TOK fofUnitaryFormula[expr] { args.push_back(expr); } )+
        { expr = MK_EXPR(kind::OR,args); }
      )
   )?
  ;

fofUnitaryFormula[CVC4::Expr & expr]
@declarations{
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
  } ;

bindvariable[CVC4::Expr & expr]
  : UPPER_WORD
    {
      std::string name = AntlrInput::tokenText($UPPER_WORD);
      expr = PARSER_STATE->mkBoundVar(name, PARSER_STATE->d_unsorted);
    }
    ;

fofBinaryNonAssoc[CVC4::parser::tptp::NonAssoc & na]
  : IFF_TOK      { na = tptp::NA_IFF; }
  | REVIFF_TOK   { na = tptp::NA_REVIFF; }
  | REVOR_TOK    { na = tptp::NA_REVOR; }
  | REVAND_TOK   { na = tptp::NA_REVAND; }
  | IMPLIES_TOK    { na = tptp::NA_IMPLIES; }
  | REVIMPLIES_TOK { na = tptp::NA_REVIMPLIES; }
  ;

folQuantifier[CVC4::Kind & kind]
  : BANG_TOK { kind = kind::FORALL; }
  | MARK_TOK { kind = kind::EXISTS; }
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
unquotedFileName[std::string & name] /* Beware fileName identifier is used by the backend ... */
 : (s=LOWER_WORD_SINGLE_QUOTED | s=SINGLE_QUOTED)
    { name = AntlrInput::tokenText($s);
      name = name.substr(1, name.size() - 2 );
    };

/* axiom name */
nameN[std::string & name]
 : atomicWord[name]
 | NUMBER { name = AntlrInput::tokenText($NUMBER); }
 ;

/* atomic word everything (fof, cnf, thf, tff, include must not be keyword at this position ) */
atomicWord[std::string & name]
 : FOF_TOK     { name = "fof"; }
 | CNF_TOK     { name = "cnf"; }
 | THF_TOK     { name = "thf"; }
 | TFF_TOK     { name = "tff"; }
 | INCLUDE_TOK { name = "include"; }
 | LOWER_WORD  { name = AntlrInput::tokenText($LOWER_WORD); }
 | LOWER_WORD_SINGLE_QUOTED //the lower word single quoted are considered without quote
    {
      /* strip off the quotes */
      name = AntlrInput::tokenTextSubstr($LOWER_WORD_SINGLE_QUOTED,1,
                                         ($LOWER_WORD_SINGLE_QUOTED->stop - $LOWER_WORD_SINGLE_QUOTED->start) - 1);
    }
 | SINGLE_QUOTED {name = AntlrInput::tokenText($SINGLE_QUOTED); }; //for the others the quote remains

/** I don't understand how is made the difference between rational and real in SyntaxBNF. So I put all in rational */
/* Rational */

fragment DOT              : '.';
fragment EXPONENT         : 'E'|'e';
fragment SLASH            : '/';

fragment DECIMAL : NUMERIC+;

/* Currently we put all in the rationnal type */
fragment SIGN[bool & pos] : PLUS_TOK | MINUS_TOK { pos = false; } ;


NUMBER
@declarations{
  bool pos = true;
  bool posE = true;
}
  :
  ( SIGN[pos]? num=DECIMAL
    {
      Integer i (AntlrInput::tokenText($num));
      Rational r = ( pos ? i : -i );
      PARSER_STATE->d_tmp_expr = MK_CONST(r);
    }
  | SIGN[pos]? num=DECIMAL DOT den=DECIMAL (EXPONENT SIGN[posE]? e=DECIMAL)?
    {
        std::string snum = AntlrInput::tokenText($num);
        std::string sden = AntlrInput::tokenText($den);
        /* compute the numerator */
        Integer inum( snum + sden );
        // The sign
        inum = pos ? inum : - inum;
        // The exponent
        size_t exp = ($e == NULL ? 0 : AntlrInput::tokenToUnsigned($e));
        // Decimal part
        size_t dec = sden.size();
        /* multiply it by 10 raised to the exponent reduced by the
         * number of decimal place in den (dec) */
        Rational r;
        if( !posE ) r = Rational(inum, Integer(10).pow(exp + dec));
        else if( exp == dec ) r = Rational(inum);
        else if( exp > dec ) r = Rational(inum * Integer(10).pow(exp - dec));
        else r = Rational(inum, Integer(10).pow(dec - exp));
        PARSER_STATE->d_tmp_expr = MK_CONST( r );
      }
  | SIGN[pos]? num=DECIMAL SLASH den=DECIMAL
    {
      Integer inum(AntlrInput::tokenText($num));
      Integer iden(AntlrInput::tokenText($den));
      PARSER_STATE->d_tmp_expr = MK_CONST(
        Rational(pos ? inum : -inum, iden));
    }
  ) {
      //Put a convertion around it
      PARSER_STATE->d_tmp_expr = PARSER_STATE->convertRatToUnsorted( PARSER_STATE->d_tmp_expr );
    }
  ;


/**
 * Matches the comments and ignores them
 */
COMMENT
  : '%' (~('\n' | '\r'))*     { SKIP(); }     //comment line
  | '/*'  ( options {greedy=false;} : . )*  '*/' { SKIP(); } //comment block
  ;




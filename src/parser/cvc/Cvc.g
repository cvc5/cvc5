/* *******************                                                        */
/*  Cvc.g
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser for CVC-LIB input language.
 **/

grammar Cvc;

options {
  language = 'C';                  // C output for antlr
//  defaultErrorHandler = false;      // Skip the default error handling, just break with exceptions
  k = 2;
}

@header {
/**
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **/
}

@lexer::includes {
/** This suppresses warnings about the redefinition of token symbols between different
  * parsers. The redefinitions should be harmless as long as no client: (a) #include's 
  * the lexer headers for two grammars AND (b) uses the token symbol definitions. */
#pragma GCC system_header

/* This improves performance by ~10 percent on big inputs.
 * This option is only valid if we know the input is ASCII (or some 8-bit encoding).
 * If we know the input is UTF-16, we can use ANTLR3_INLINE_INPUT_UTF16.
 * Otherwise, we have to let the lexer detect the encoding at runtime.
 */
#define ANTLR3_INLINE_INPUT_ASCII
}

@parser::includes {
#include "expr/command.h"
#include "parser/parser_state.h"

namespace CVC4 {
  class Expr;
}
}

@parser::postinclude {
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser_state.h"
#include "util/output.h"
#include <vector>

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE 
#define PARSER_STATE ((ParserState*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst
}


/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::Expr expr]
  : formula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd]
  : c = command { $cmd = c; }
  ;

/**
 * Matches a command of the input. If a declaration, it will return an empty
 * command.
 */
command returns [CVC4::Command* cmd = 0]
@init {
  Expr f;
  Debug("parser-extra") << "command: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : ASSERT_TOK formula[f] SEMICOLON { cmd = new AssertCommand(f);   }
  | QUERY_TOK formula[f] SEMICOLON { cmd = new QueryCommand(f);    }
  | CHECKSAT_TOK formula[f] SEMICOLON { cmd = new CheckSatCommand(f); }
  | CHECKSAT_TOK SEMICOLON { cmd = new CheckSatCommand(MK_CONST(true)); }
  | PUSH_TOK SEMICOLON { cmd = new PushCommand(); }
  | POP_TOK SEMICOLON { cmd = new PopCommand(); }
  | declaration[cmd]
  | EOF
  ;

/**
 * Match a declaration
 */

declaration[CVC4::Command*& cmd]
@init {
  std::vector<std::string> ids;
  Type* t;
  Debug("parser-extra") << "declaration: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : // FIXME: These could be type or function declarations, if that matters.
    identifierList[ids, CHECK_UNDECLARED, SYM_VARIABLE] COLON declType[t,ids] SEMICOLON
    { cmd = new DeclarationCommand(ids,t); }
  ;

/** Match the right-hand side of a declaration. Returns the type. */
declType[CVC4::Type*& t, std::vector<std::string>& idList]
@init {
  Debug("parser-extra") << "declType: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* A sort declaration (e.g., "T : TYPE") */
    TYPE_TOK 
    { PARSER_STATE->mkSorts(idList); 
      t = EXPR_MANAGER->kindType(); }
  | /* A variable declaration */
    type[t] { PARSER_STATE->mkVars(idList,t); }
  ;

/**
 * Match the type in a declaration and do the declaration binding.
 * TODO: Actually parse sorts into Type objects.
 */
type[CVC4::Type*& t]
@init {
  Type* t2;
  std::vector<Type*> typeList;
  Debug("parser-extra") << "type: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* Simple type */
    baseType[t]
  | /* Single-parameter function type */
    baseType[t] ARROW_TOK baseType[t2] 
    { t = EXPR_MANAGER->mkFunctionType(t,t2); }
  | /* Multi-parameter function type */
    LPAREN baseType[t]
    { typeList.push_back(t); }
    (COMMA baseType[t] { typeList.push_back(t); } )+
    RPAREN ARROW_TOK baseType[t]
    { t = EXPR_MANAGER->mkFunctionType(typeList,t); }
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
}
  : identifier[id,check,type] { idList.push_back(id); }
    (COMMA identifier[id,check,type] { idList.push_back(id); })*
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
 * Matches a type.
 * TODO: parse more types
 */
baseType[CVC4::Type*& t]
@init {
  std::string id;
  Debug("parser-extra") << "base type: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : BOOLEAN_TOK { t = EXPR_MANAGER->booleanType(); }
  | typeSymbol[t]
  ;

/**
 * Matches a type identifier
 */
typeSymbol[CVC4::Type*& t]
@init {
  std::string id;
  Debug("parser-extra") << "type symbol: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : identifier[id,CHECK_DECLARED,SYM_SORT]
    { t = PARSER_STATE->getSort(id); }
  ;

/**
 * Matches a CVC4 formula.
 * @return the expression representing the formula
 */
formula[CVC4::Expr& formula]
@init {
  Debug("parser-extra") << "formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  :  iffFormula[formula]
  ;

/**
 * Matches a comma-separated list of formulas
 */
formulaList[std::vector<CVC4::Expr>& formulas]
@init {
  Expr f;
}
  : formula[f] { formulas.push_back(f); }
    ( COMMA formula[f]
      { formulas.push_back(f); }
    )*
  ;

/**
 * Matches a Boolean IFF formula (right-associative)
 */
iffFormula[CVC4::Expr& f]
@init {
  Expr e;
  Debug("parser-extra") << "<=> formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : impliesFormula[f]
    ( IFF_TOK 
    	iffFormula[e]
        { f = MK_EXPR(CVC4::kind::IFF, f, e); }
    )?
  ;

/**
 * Matches a Boolean IMPLIES formula (right-associative)
 */
impliesFormula[CVC4::Expr& f]
@init {
  Expr e;
  Debug("parser-extra") << "=> Formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : orFormula[f]
    ( IMPLIES_TOK impliesFormula[e]
        { f = MK_EXPR(CVC4::kind::IMPLIES, f, e); }
    )?
  ;

/**
 * Matches a Boolean OR formula (left-associative)
 */
orFormula[CVC4::Expr& f]
@init {
  std::vector<Expr> exprs;
  Debug("parser-extra") << "OR Formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : xorFormula[f]
      ( OR_TOK  { exprs.push_back(f); }
        xorFormula[f] { exprs.push_back(f); } )*
    {
      if( exprs.size() > 0 ) {
        f = MK_EXPR(CVC4::kind::OR, exprs);
      }
    }
  ;

/**
 * Matches a Boolean XOR formula (left-associative)
 */
xorFormula[CVC4::Expr& f]
@init {
  Expr e;
  Debug("parser-extra") << "XOR formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : andFormula[f]
    ( XOR_TOK andFormula[e]
      { f = MK_EXPR(CVC4::kind::XOR,f, e); }
    )*
  ;

/**
 * Matches a Boolean AND formula (left-associative)
 */
andFormula[CVC4::Expr& f]
@init {
  std::vector<Expr> exprs;
  Debug("parser-extra") << "AND Formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : notFormula[f] 
    ( AND_TOK { exprs.push_back(f); }
      notFormula[f] { exprs.push_back(f); } )*
    {
      if( exprs.size() > 0 ) {
        f = MK_EXPR(CVC4::kind::AND, exprs);
      }
    }
  ;

/**
 * Parses a NOT formula.
 * @return the expression representing the formula
 */
notFormula[CVC4::Expr& f]
@init {
  Debug("parser-extra") << "NOT formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* negation */
    NOT_TOK notFormula[f]
    { f = MK_EXPR(CVC4::kind::NOT, f); }
  | /* a boolean atom */
    predFormula[f]
  ;

predFormula[CVC4::Expr& f]
@init {
  Expr e;
  Debug("parser-extra") << "predicate formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : term[f]
    (EQUAL_TOK term[e]
      { f = MK_EXPR(CVC4::kind::EQUAL, f, e); }
    )?
  ; // TODO: lt, gt, etc.

/**
 * Parses a term.
 */
term[CVC4::Expr& f]
@init {
  std::string name;
  std::vector<Expr> args;
  Debug("parser-extra") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* function application */
    // { isFunction(AntlrInput::tokenText(LT(1))) }?
    functionSymbol[f]
    { args.push_back( f ); }
    LPAREN formulaList[args] RPAREN
    // TODO: check arity
    { f = MK_EXPR(CVC4::kind::APPLY_UF, args); }

  | /* if-then-else */
    iteTerm[f]

  | /* parenthesized sub-formula */
    LPAREN formula[f] RPAREN

    /* constants */
  | TRUE_TOK  { f = MK_CONST(true); }
  | FALSE_TOK { f = MK_CONST(false); }

  | /* variable */
    identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    { f = PARSER_STATE->getVariable(name); }
  ;

/**
 * Parses an ITE term.
 */
iteTerm[CVC4::Expr& f]
@init {
  std::vector<Expr> args;
  Debug("parser-extra") << "ite: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : IF_TOK formula[f] { args.push_back(f); }
    THEN_TOK formula[f] { args.push_back(f); }
    iteElseTerm[f] { args.push_back(f); }
    ENDIF_TOK
    { f = MK_EXPR(CVC4::kind::ITE, args); }
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseTerm[CVC4::Expr& f]
@init {
  std::vector<Expr> args;
  Debug("parser-extra") << "else: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : ELSE_TOK formula[f] 
  | ELSEIF_TOK iteCondition = formula[f] { args.push_back(f); }
    THEN_TOK iteThen = formula[f] { args.push_back(f); }
    iteElse = iteElseTerm[f] { args.push_back(f); }
    { f = MK_EXPR(CVC4::kind::ITE, args); }
  ;

/**
 * Parses a function symbol (an identifier).
 * @param what kind of check to perform on the id
 * @return the predicate symol
 */
functionSymbol[CVC4::Expr& f]
@init {
  Debug("parser-extra") << "function symbol: " << AntlrInput::tokenText(LT(1)) << std::endl;
  std::string name;
}
  : identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    { PARSER_STATE->checkFunction(name);
      f = PARSER_STATE->getVariable(name); }
  ;


// Keywords

AND_TOK : 'AND';
ASSERT_TOK : 'ASSERT';
BOOLEAN_TOK : 'BOOLEAN';
CHECKSAT_TOK : 'CHECKSAT';
ECHO_TOK : 'ECHO';
ELSEIF_TOK : 'ELSIF';
ELSE_TOK : 'ELSE';
ENDIF_TOK : 'ENDIF';
FALSE_TOK : 'FALSE';
IF_TOK : 'IF';
NOT_TOK : 'NOT';
OR_TOK : 'OR';
POPTO_TOK : 'POPTO';
POP_TOK : 'POP';
PRINT_TOK : 'PRINT';
PUSH_TOK : 'PUSH';
QUERY_TOK : 'QUERY';
THEN_TOK : 'THEN';
TRUE_TOK : 'TRUE';
TYPE_TOK : 'TYPE';
XOR_TOK : 'XOR';

// Symbols

COLON : ':';
COMMA : ',';
LPAREN : '(';
RPAREN : ')';
SEMICOLON : ';';

// Operators

IMPLIES_TOK : '=>';
IFF_TOK     : '<=>';
ARROW_TOK : '->';
EQUAL_TOK   : '=';

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER : ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
NUMERAL: (DIGIT)+;

/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment ALPHA : 'a'..'z' | 'A'..'Z';

/**
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

/**
 * Matches and skips whitespace in the input and ignores it.
 */
WHITESPACE : (' ' | '\t' | '\f' | '\r' | '\n') { $channel = HIDDEN;; };

/**
 * Matches the comments and ignores them
 */
COMMENT : '%' (~('\n' | '\r'))* { $channel = HIDDEN;; };


/* *******************                                                        */
/*  Smt.g
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
 ** Parser for SMT-LIB input language.
 **/

grammar Smt;

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
}

@parser::includes {
#include "expr/command.h"
#include "parser/parser.h"

namespace CVC4 {
  class Expr;
}
}

@parser::postinclude {
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "util/integer.h"
#include "util/output.h"
#include "util/rational.h"
#include <vector>

using namespace CVC4;
using namespace CVC4::parser;

/* These need to be macros so they can refer to the PARSER macro, which will be defined
 * by ANTLR *after* this section. (If they were functions, PARSER would be undefined.) */
#undef PARSER_STATE 
#define PARSER_STATE ((Parser*)PARSER->super)
#undef EXPR_MANAGER
#define EXPR_MANAGER PARSER_STATE->getExprManager()
#undef MK_EXPR
#define MK_EXPR EXPR_MANAGER->mkExpr
#undef MK_CONST
#define MK_CONST EXPR_MANAGER->mkConst

/**   
 * Sets the logic for the current benchmark. Declares any logic symbols.
 *
 * @param parser the CVC4 Parser object
 * @param name the name of the logic (e.g., QF_UF, AUFLIA)
 */
static void
setLogic(Parser *parser, const std::string& name) {
  if( name == "QF_UF" ) {
    parser->mkSort("U");
  } else if(name == "QF_LRA"){
    parser->defineType("Real", parser->getExprManager()->realType());
  } else{
    // NOTE: Theory types go here
    Unhandled(name);
  }
}
}


/**
 * Parses an expression.
 * @return the parsed expression
 */
parseExpr returns [CVC4::Expr expr]
  : annotatedFormula[expr]
  | EOF
  ;

/**
 * Parses a command (the whole benchmark)
 * @return the command of the benchmark
 */
parseCommand returns [CVC4::Command* cmd]
  : b = benchmark { $cmd = b; }
  ;

/**
 * Matches the whole SMT-LIB benchmark.
 * @return the sequence command containing the whole problem
 */
benchmark returns [CVC4::Command* cmd]
  : LPAREN_TOK BENCHMARK_TOK IDENTIFIER c = benchAttributes RPAREN_TOK 
  	{ $cmd = c; }
  | EOF { $cmd = 0; }
  ;

/**
 * Matches a sequence of benchmark attributes and returns a pointer to a
 * command sequence.
 * @return the command sequence
 */
benchAttributes returns [CVC4::CommandSequence* cmd_seq]
@init {
  cmd_seq = new CommandSequence();
}
  : (cmd = benchAttribute { if (cmd) cmd_seq->addCommand(cmd); } )+
  ;

/**
 * Matches a benchmark attribute, sucha as ':logic', ':formula', and returns
 * a corresponding command
 * @return a command corresponding to the attribute
 */
benchAttribute returns [CVC4::Command* smt_command]
@declarations { 
  std::string name;
  BenchmarkStatus b_status;
  Expr expr;
}
  : LOGIC_TOK identifier[name,CHECK_NONE,SYM_VARIABLE]
    { setLogic(PARSER_STATE,name);
      smt_command = new SetBenchmarkLogicCommand(name);   }
  | ASSUMPTION_TOK annotatedFormula[expr]
    { smt_command = new AssertCommand(expr);   }
  | FORMULA_TOK annotatedFormula[expr]
    { smt_command = new CheckSatCommand(expr); }
  | STATUS_TOK status[b_status]                   
    { smt_command = new SetBenchmarkStatusCommand(b_status); }        
  | EXTRAFUNS_TOK LPAREN_TOK (functionDeclaration)+ RPAREN_TOK  
  | EXTRAPREDS_TOK LPAREN_TOK (predicateDeclaration)+ RPAREN_TOK  
  | EXTRASORTS_TOK LPAREN_TOK sortDeclaration+ RPAREN_TOK  
  | NOTES_TOK STRING_LITERAL        
  | annotation
  ;

/**
 * Matches an annotated formula.
 * @return the expression representing the formula
 */
annotatedFormula[CVC4::Expr& expr]
@init {
  Debug("parser") << "annotated formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
  Kind kind;
  std::string name;
  std::vector<Expr> args; /* = getExprVector(); */
  Expr op; /* Operator expression FIXME: move away kill it */
} 
  : /* a built-in operator application */
    LPAREN_TOK builtinOp[kind] annotatedFormulas[args,expr] RPAREN_TOK 
    { if((kind == CVC4::kind::AND || kind == CVC4::kind::OR) && args.size() == 1) {
        /* Unary AND/OR can be replaced with the argument.
	       It just so happens expr should already by the only argument. */
        Assert( expr == args[0] );
      } else {
        PARSER_STATE->checkArity(kind, args.size());
        expr = MK_EXPR(kind, args);
      }
    }

  | /* A non-built-in function application */

    // Semantic predicate not necessary if parenthesized subexpressions
    // are disallowed
    // { isFunction(LT(2)->getText()) }? 	
    LPAREN_TOK 
    parameterizedOperator[op]
    annotatedFormulas[args,expr] RPAREN_TOK
    // TODO: check arity
    { expr = MK_EXPR(op,args); }

  | /* An ite expression */
    LPAREN_TOK ITE_TOK 
    annotatedFormula[expr]
    { args.push_back(expr); } 
    annotatedFormula[expr]
    { args.push_back(expr); } 
    annotatedFormula[expr]
    { args.push_back(expr); } 
    RPAREN_TOK
    { expr = MK_EXPR(CVC4::kind::ITE, args); }

  | /* a let/flet binding */
    LPAREN_TOK 
    (LET_TOK LPAREN_TOK let_identifier[name,CHECK_UNDECLARED]
      | FLET_TOK LPAREN_TOK flet_identifier[name,CHECK_UNDECLARED] )
    annotatedFormula[expr] RPAREN_TOK
    { PARSER_STATE->pushScope();
      PARSER_STATE->defineVar(name,expr); }
    annotatedFormula[expr]
    RPAREN_TOK
    { PARSER_STATE->popScope(); }

  | /* a variable */
    ( identifier[name,CHECK_DECLARED,SYM_VARIABLE]
      | let_identifier[name,CHECK_DECLARED] 
      | flet_identifier[name,CHECK_DECLARED] )
    { expr = PARSER_STATE->getVariable(name); }

    /* constants */
  | TRUE_TOK          { expr = MK_CONST(true); }
  | FALSE_TOK         { expr = MK_CONST(false); }
  | NUMERAL_TOK
    { expr = MK_CONST( AntlrInput::tokenToInteger($NUMERAL_TOK) ); }
  | RATIONAL_TOK
    { // FIXME: This doesn't work because an SMT rational is not a valid GMP rational string
      expr = MK_CONST( AntlrInput::tokenToRational($RATIONAL_TOK) ); }
    // NOTE: Theory constants go here
    /* TODO: quantifiers, arithmetic constants */
  ;

/**
 * Matches a sequence of annotated formulas and puts them into the formulas
 * vector.
 * @param formulas the vector to fill with formulas
 * @param expr an Expr reference for the elements of the sequence
 */   
/* NOTE: We pass an Expr in here just to avoid allocating a fresh Expr every 
 * time through this rule. */
annotatedFormulas[std::vector<CVC4::Expr>& formulas, CVC4::Expr& expr]
  : ( annotatedFormula[expr] { formulas.push_back(expr); } )+
  ;

/**
* Matches a builtin operator symbol and sets kind to its associated Expr kind.
*/
builtinOp[CVC4::Kind& kind]
@init {
  Debug("parser") << "builtin: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : NOT_TOK      { $kind = CVC4::kind::NOT;     }
  | IMPLIES_TOK  { $kind = CVC4::kind::IMPLIES; }
  | AND_TOK      { $kind = CVC4::kind::AND;     }
  | OR_TOK       { $kind = CVC4::kind::OR;      }
  | XOR_TOK      { $kind = CVC4::kind::XOR;     }
  | IFF_TOK      { $kind = CVC4::kind::IFF;     }
  | EQUAL_TOK    { $kind = CVC4::kind::EQUAL;   }
  | DISTINCT_TOK { $kind = CVC4::kind::DISTINCT; }
  | GREATER_THAN_TOK
                 { $kind = CVC4::kind::GT; }
  | GREATER_THAN_TOK EQUAL_TOK
                 { $kind = CVC4::kind::GEQ; }
  | LESS_THAN_TOK EQUAL_TOK
                 { $kind = CVC4::kind::LEQ; }
  | LESS_THAN_TOK
                 { $kind = CVC4::kind::LT; }
  | PLUS_TOK     { $kind = CVC4::kind::PLUS; }
  | STAR_TOK     { $kind = CVC4::kind::MULT; }
  | TILDE_TOK    { $kind = CVC4::kind::UMINUS; }
  | MINUS_TOK    { $kind = CVC4::kind::MINUS; }
  // Bit-vectors
    // NOTE: Theory operators go here
    /* TODO: lt, gt, plus, minus, etc. */
  ;

/**
 * Matches an operator.
 */
parameterizedOperator[CVC4::Expr& op] 
  : functionSymbol[op]
  ;

/**
 * Matches a (possibly undeclared) predicate identifier (returning the string). 
 * @param check what kind of check to do with the symbol
 */
predicateName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  functionName[name,check]
  ;

/**
 * Matches a (possibly undeclared) function identifier (returning the string)
 * @param check what kind of check to do with the symbol
 */
functionName[std::string& name, CVC4::parser::DeclarationCheck check]
  :  identifier[name,check,SYM_VARIABLE] 
  ;

/**
 * Matches an previously declared function symbol (returning an Expr)
 */
functionSymbol[CVC4::Expr& fun]
@declarations {
	std::string name;
}
  : functionName[name,CHECK_DECLARED]
    { PARSER_STATE->checkFunction(name);
      fun = PARSER_STATE->getVariable(name); }
  ;
  
/**
 * Matches an attribute name from the input (:attribute_name).
 */
attribute
  :  ATTR_IDENTIFIER
  ;

functionDeclaration
@declarations {
  std::string name;
  std::vector<Type> sorts;
}
  : LPAREN_TOK functionName[name,CHECK_UNDECLARED] 
      t = sortSymbol // require at least one sort
    { sorts.push_back(t); }
      sortList[sorts] RPAREN_TOK
    { if( sorts.size() == 1 ) {
        Assert( t == sorts[0] ); 
      } else {
        t = EXPR_MANAGER->mkFunctionType(sorts);
      }
      PARSER_STATE->mkVar(name, t); } 
  ;
              
/**
 * Matches the declaration of a predicate and declares it
 */
predicateDeclaration
@declarations {
  std::string name;
  std::vector<Type> p_sorts;
}
  : LPAREN_TOK predicateName[name,CHECK_UNDECLARED] sortList[p_sorts] RPAREN_TOK
    { Type t;
      if( p_sorts.empty() ) {
        t = EXPR_MANAGER->booleanType();
      } else { 
        t = EXPR_MANAGER->mkPredicateType(p_sorts);
      }
      PARSER_STATE->mkVar(name, t); } 
  ;

sortDeclaration 
@declarations {
  std::string name;
}
  : sortName[name,CHECK_UNDECLARED]
    { Debug("parser") << "sort decl: '" << name << "'" << std::endl;
      PARSER_STATE->mkSort(name); }
  ;
  
/**
 * Matches a sequence of sort symbols and fills them into the given vector.
 */
sortList[std::vector<CVC4::Type>& sorts]
  : ( t = sortSymbol { sorts.push_back(t); })* 
  ;

/**
 * Matches the sort symbol, which can be an arbitrary identifier.
 * @param check the check to perform on the name
 */
sortName[std::string& name, CVC4::parser::DeclarationCheck check] 
  : identifier[name,check,SYM_SORT] 
  ;

sortSymbol returns [CVC4::Type t]
@declarations {
  std::string name;
}
  : sortName[name,CHECK_NONE] 
  	{ $t = PARSER_STATE->getSort(name); }
  ;

/**
 * Matches the status of the benchmark, one of 'sat', 'unsat' or 'unknown'.
 */
status[ CVC4::BenchmarkStatus& status ]
  : SAT_TOK       { $status = SMT_SATISFIABLE;    }
  | UNSAT_TOK     { $status = SMT_UNSATISFIABLE;  }
  | UNKNOWN_TOK   { $status = SMT_UNKNOWN;        }
  ;

/**
 * Matches an annotation, which is an attribute name, with an optional user
 */
annotation
  : attribute (USER_VALUE)?
  ;

/**
 * Matches an identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 * @param type the intended namespace for the identifier
 */
identifier[std::string& id,
		   CVC4::parser::DeclarationCheck check, 
           CVC4::parser::SymbolType type] 
  : IDENTIFIER
    { id = AntlrInput::tokenText($IDENTIFIER);
      Debug("parser") << "identifier: " << id
                      << " check? " << toString(check)
                      << " type? " << toString(type) << std::endl;
      PARSER_STATE->checkDeclaration(id, check, type); }
  ;

/**
 * Matches a let-bound identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 */
let_identifier[std::string& id,
    		   CVC4::parser::DeclarationCheck check] 
  : LET_IDENTIFIER
    { id = AntlrInput::tokenText($LET_IDENTIFIER);
      Debug("parser") << "let_identifier: " << id
                      << " check? " << toString(check) << std::endl;
      PARSER_STATE->checkDeclaration(id, check, SYM_VARIABLE); }
  ;

/**
 * Matches an flet-bound identifier and sets the string reference parameter id.
 * @param id string to hold the identifier
 * @param check what kinds of check to do on the symbol
 */
flet_identifier[std::string& id,
    		    CVC4::parser::DeclarationCheck check] 
  : FLET_IDENTIFIER
    { id = AntlrInput::tokenText($FLET_IDENTIFIER);
      Debug("parser") << "flet_identifier: " << id
                      << " check? " << toString(check) << std::endl;
      PARSER_STATE->checkDeclaration(id, check); }
  ;

// Base SMT-LIB tokens
ASSUMPTION_TOK  : ':assumption';
BENCHMARK_TOK   : 'benchmark';
EXTRAFUNS_TOK   : ':extrafuns';
EXTRAPREDS_TOK  : ':extrapreds';
EXTRASORTS_TOK  : ':extrasorts';
FALSE_TOK       : 'false';
FLET_TOK        : 'flet';
FORMULA_TOK     : ':formula';
ITE_TOK         : 'ite' | 'if_then_else';
LET_TOK         : 'let';
LOGIC_TOK       : ':logic';
LPAREN_TOK      : '(';
NOTES_TOK       : ':notes';
RPAREN_TOK      : ')';
SAT_TOK         : 'sat';
STATUS_TOK      : ':status';
THEORY_TOK      : 'theory';
TRUE_TOK        : 'true';
UNKNOWN_TOK     : 'unknown';
UNSAT_TOK       : 'unsat';

// operators (NOTE: theory symbols go here)
AMPERSAND_TOK     : '&';
AND_TOK           : 'and';
AT_TOK            : '@';
DISTINCT_TOK      : 'distinct';
DIV_TOK           : '/';
EQUAL_TOK         : '=';
EXISTS_TOK        : 'exists';
FORALL_TOK        : 'forall';
GREATER_THAN_TOK  : '>';
IFF_TOK           : 'iff';
IMPLIES_TOK       : 'implies';
LESS_THAN_TOK     : '<';
MINUS_TOK         : '-';
NOT_TOK           : 'not';
OR_TOK            : 'or';
PERCENT_TOK       : '%';
PIPE_TOK          : '|';
PLUS_TOK          : '+';
POUND_TOK         : '#';
STAR_TOK          : '*';
TILDE_TOK         : '~';
XOR_TOK           : 'xor';


/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER
  :  ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*
  ;

/**
 * Matches an identifier starting with a colon.
 */
ATTR_IDENTIFIER 
  :  ':' IDENTIFIER
  ;

/**
 * Matches an identifier starting with a question mark.
 */
LET_IDENTIFIER
  : '?' IDENTIFIER
  ;
  
/**
 * Matches an identifier starting with a dollar sign.
 */
FLET_IDENTIFIER
  : '$' IDENTIFIER
  ;

/**
 * Matches the value of user-defined annotations or attributes. The only constraint imposed on a user-defined value is that it start with
 * an open brace and end with closed brace.
 */
USER_VALUE
  :   '{'
      ( ~('{' | '}') )*
    '}'
  ;


/**
 * Matches and skips whitespace in the input.
 */
WHITESPACE
  :  (' ' | '\t' | '\f' | '\r' | '\n')+             { $channel = HIDDEN;; }
  ;

/**
 * Matches a numeral from the input (non-empty sequence of digits).
 */
NUMERAL_TOK
  : DIGIT+
  ;

RATIONAL_TOK
  : DIGIT+ '.' DIGIT+
  ;

/**
 * Matches a double quoted string literal. Escaping is supported, and escape
 * character '\' has to be escaped.
 */
STRING_LITERAL 
  :  '"' (ESCAPE | ~('"'|'\\'))* '"'
  ;

/**
 * Matches the comments and ignores them
 */
COMMENT 
  : ';' (~('\n' | '\r'))*                    { $channel = HIDDEN;; }
  ;


/**
 * Matches any letter ('a'-'z' and 'A'-'Z').
 */
fragment
ALPHA 
  :  'a'..'z'
  |  'A'..'Z'
  ;

/**
 * Matches the digits (0-9)
 */
fragment DIGIT :   '0'..'9';
// fragment NON_ZERO_DIGIT : '1'..'9';
// fragment NUMERAL_SEQ : '0' | NON_ZERO_DIGIT DIGIT*;

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');


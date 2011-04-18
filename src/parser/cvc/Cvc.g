/* *******************                                                        */
/*! \file Cvc.g
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser for CVC-LIB input language.
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
#include "parser/parser.h"

namespace CVC4 {
  class Expr;
}/* CVC4 namespace */

namespace CVC4 {
  namespace parser {
    namespace cvc {
      /**
       * This class is just here to get around an unfortunate bit of Antlr.
       * We use strings below as return values from rules, which require
       * them to be constructible by a uintptr_t.  So we derive the string
       * class to provide just such a conversion.
       */
      class mystring : public std::string {
      public:
        mystring(const std::string& s) : std::string(s) {}
        mystring(uintptr_t) : std::string() {}
        mystring() : std::string() {}
      };/* class mystring */
    }/* CVC4::parser::cvc namespace */
  }/* CVC4::parser namespace */
}/* CVC4 namespace */

}

@parser::postinclude {
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "parser/antlr_input.h"
#include "parser/parser.h"
#include "util/output.h"
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
  SExpr sexpr;
  std::string s;
  Type t;
  std::vector<CVC4::Datatype> dts;
  Debug("parser-extra") << "command: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : ASSERT_TOK formula[f] SEMICOLON { cmd = new AssertCommand(f);   }
  | QUERY_TOK formula[f] SEMICOLON { cmd = new QueryCommand(f);    }
  | CHECKSAT_TOK formula[f] SEMICOLON { cmd = new CheckSatCommand(f); }
  | CHECKSAT_TOK SEMICOLON { cmd = new CheckSatCommand(MK_CONST(true)); }
  | OPTION_TOK STRING_LITERAL symbolicExpr[sexpr] SEMICOLON
    { cmd = new SetOptionCommand(AntlrInput::tokenText($STRING_LITERAL), sexpr); }
  | PUSH_TOK SEMICOLON { cmd = new PushCommand(); }
  | POP_TOK SEMICOLON { cmd = new PopCommand(); }
    // Datatypes can be mututally-recursive if they're in the same
    // definition block, separated by a comma.  So we parse everything
    // and then ask the ExprManager to resolve everything in one go.
  | DATATYPE_TOK datatypeDef[dts]
    ( COMMA datatypeDef[dts] )*
    END_TOK SEMICOLON
    { cmd = new DatatypeDeclarationCommand(PARSER_STATE->mkMutualDatatypeTypes(dts)); }
  | declaration[cmd]
  | EOF
  ;

symbolicExpr[CVC4::SExpr& sexpr]
@declarations {
  std::vector<SExpr> children;
}
  : INTEGER_LITERAL
    { sexpr = SExpr(AntlrInput::tokenText($INTEGER_LITERAL)); }
  | DECIMAL_LITERAL
    { sexpr = SExpr(AntlrInput::tokenText($DECIMAL_LITERAL)); }
  | STRING_LITERAL
    { sexpr = SExpr(AntlrInput::tokenText($STRING_LITERAL)); }
  | IDENTIFIER
    { sexpr = SExpr(AntlrInput::tokenText($IDENTIFIER)); }
  | LPAREN (symbolicExpr[sexpr] { children.push_back(sexpr); } )* RPAREN
    { sexpr = SExpr(children); }
  ;

/**
 * Match a declaration
 */
declaration[CVC4::Command*& cmd]
@init {
  std::vector<std::string> ids;
  Type t;
  Debug("parser-extra") << "declaration: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : // FIXME: These could be type or function declarations, if that matters.
    identifierList[ids, CHECK_UNDECLARED, SYM_VARIABLE] COLON declType[t,ids] SEMICOLON
    { cmd = new DeclarationCommand(ids,t); }
  ;

/** Match the right-hand side of a declaration. Returns the type. */
declType[CVC4::Type& t, std::vector<std::string>& idList]
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
type[CVC4::Type& t]
@init {
  Type t2;
  std::vector<Type> typeList;
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
 * Matches a type (which MUST be already declared).
 *
 * @return the type identifier
 */
baseType[CVC4::Type& t]
  : maybeUndefinedBaseType[t,CHECK_DECLARED]
  ;

/**
 * Matches a type (which may not be declared yet).  Returns the
 * identifier.  If the type is declared, returns the Type in the 't'
 * parameter; otherwise a null Type is returned in 't'.  If 'check' is
 * CHECK_DECLARED and the type is not declared, an exception is
 * thrown.
 *
 * @return the type identifier
 *
 * @TODO parse more types
 */
maybeUndefinedBaseType[CVC4::Type& t,
                       CVC4::parser::DeclarationCheck check] returns [CVC4::parser::cvc::mystring id]
@init {
  Debug("parser-extra") << "base type: " << AntlrInput::tokenText(LT(1)) << std::endl;
  AssertArgument(check == CHECK_DECLARED || check == CHECK_NONE,
                 check, "CVC parser: can't use CHECK_UNDECLARED with maybeUndefinedBaseType[]");
}
  : BOOLEAN_TOK { t = EXPR_MANAGER->booleanType(); id = AntlrInput::tokenText($BOOLEAN_TOK); }
  | INT_TOK { t = EXPR_MANAGER->integerType(); id = AntlrInput::tokenText($INT_TOK); }
  | REAL_TOK { t = EXPR_MANAGER->realType(); id = AntlrInput::tokenText($REAL_TOK); }
  | typeSymbol[t,check]
    { id = $typeSymbol.id; }
  ;

/**
 * Matches a type identifier.  Returns the identifier.  If the type is
 * declared, returns the Type in the 't' parameter; otherwise a null
 * Type is returned in 't'.  If 'check' is CHECK_DECLARED and the type
 * is not declared, an exception is thrown.
 *
 * @return the type identifier
 */
typeSymbol[CVC4::Type& t,
           CVC4::parser::DeclarationCheck check] returns [CVC4::parser::cvc::mystring id]
@init {
  Debug("parser-extra") << "type symbol: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : identifier[id,check,SYM_SORT]
    { bool isNew = (check == CHECK_UNDECLARED || check == CHECK_NONE) &&
                   !PARSER_STATE->isDeclared(id, SYM_SORT);
      t = isNew ? Type() : PARSER_STATE->getSort(id);
    }
  ;

/**
 * Matches a CVC4 formula.
 *
 * @return the expression representing the formula
 */
formula[CVC4::Expr& formula]
@init {
  Debug("parser-extra") << "formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : letBinding[formula]
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
 * Matches a LET binding
 */
letBinding[CVC4::Expr& f]
@init {
}
  : LET_TOK
    { PARSER_STATE->pushScope(); }
    letDecls
    IN_TOK letBinding[f]
    { PARSER_STATE->popScope(); }
  | iffFormula[f]
  ;

/**
 * Matches (and defines) LET declarations in order.  Note this implements
 * sequential-let (think "let*") rather than simultaneous-let.
 */
letDecls
  : letDecl (COMMA letDecl)*
  ;

/**
 * Matches (and defines) a single LET declaration.
 */
letDecl
@init {
  Expr e;
  std::string name;
}
  : identifier[name,CHECK_NONE,SYM_VARIABLE] EQUAL_TOK formula[e]
    { PARSER_STATE->defineVar(name, e); }
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
    comparisonFormula[f]
  ;

/** Parses a comparison formula (non-associative).
    NOTE: equality should technically have higher precedence than
    greater-than, less-than, etc., but I don't think this will ever
    be relevant in a well-typed formula.
*/
comparisonFormula[CVC4::Expr& f]
@init {
  Expr e;
  Kind op;
  bool negate;
  Debug("parser-extra") << "predicate formula: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : plusTerm[f]
    ( ( EQUAL_TOK { op = CVC4::kind::EQUAL; negate = false; }
      | DISEQUAL_TOK { op = CVC4::kind::EQUAL; negate = true; }
      | GT_TOK { op = CVC4::kind::GT; negate = false; }
      | GEQ_TOK { op = CVC4::kind::GEQ; negate = false; }
      | LT_TOK { op = CVC4::kind::LT; negate = false; }
      | LEQ_TOK { op = CVC4::kind::LEQ; negate = false; })
      plusTerm[e]
      { f = MK_EXPR(op, f, e);
        if(negate) {
          f = MK_EXPR(CVC4::kind::NOT, f);
        }
      }
    )?
  ;

/** Parses a plus/minus term (left-associative).
    TODO: This won't take advantage of n-ary PLUS's. */
plusTerm[CVC4::Expr& f]
@init {
  Expr e;
  Kind op;
  std::vector<Expr> exprs;
  Debug("parser-extra") << "plus term: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : multTerm[f]
    ( ( PLUS_TOK { op = CVC4::kind::PLUS; }
      | MINUS_TOK { op = CVC4::kind::MINUS; } )
      multTerm[e]
      { f = MK_EXPR(op, f, e); }
    )*
  ;

/** Parses a multiply/divide term (left-associative).
    TODO: This won't take advantage of n-ary MULT's. */
multTerm[CVC4::Expr& f]
@init {
  Expr e;
  Kind op;
  Debug("parser-extra") << "multiplication term: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : expTerm[f]
    ( ( STAR_TOK { op = CVC4::kind::MULT; }
      | DIV_TOK { op = CVC4::kind::DIVISION; } )
      expTerm[e]
      { f = MK_EXPR(op, f, e); }
    )*
  ;

/**
 * Parses an exponential term (left-associative).
 * NOTE that the exponent must be a nonnegative integer constant
 * (for now).
 */
expTerm[CVC4::Expr& f]
@init {
  Expr e;
  Debug("parser-extra") << "exponential term: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : unaryTerm[f]
    ( EXP_TOK INTEGER_LITERAL
      { Integer n = AntlrInput::tokenToInteger($INTEGER_LITERAL);
        if(n == 0) {
          f = MK_CONST( Integer(1) );
        } else if(n == 1) {
          /* f remains the same */
        } else {
          std::vector<Expr> v;
          for(Integer i = 0; i < n; i = i + 1) {
            v.push_back(f);
          }
          f = MK_EXPR(CVC4::kind::MULT, v);
        }
      }
    )*
  ;

/**
 * Parses a unary term.
 */
unaryTerm[CVC4::Expr& f]
@init {
  std::string name;
  std::vector<Expr> args;
  Debug("parser-extra") << "term: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* function/constructor application */
    functionSymbol[f]
    { args.push_back( f ); }
    LPAREN formulaList[args] RPAREN
    // TODO: check arity
    { Type t = f.getType();
      if( t.isFunction() ) {
        f = MK_EXPR(CVC4::kind::APPLY_UF, args);
      } else if( t.isConstructor() ) {
        Debug("parser-idt") << "apply constructor: " << name.c_str() << " " << args.size() << std::endl;
        f = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, args);
      } else if( t.isSelector() ) {
        Debug("parser-idt") << "apply selector: " << name.c_str() << " " << args.size() << std::endl;
        f = MK_EXPR(CVC4::kind::APPLY_SELECTOR, args);
      } else if( t.isTester() ) {
        Debug("parser-idt") << "apply tester: " << name.c_str() << " " << args.size() << std::endl;
        f = MK_EXPR(CVC4::kind::APPLY_TESTER, args);
      }
    }

  | /* if-then-else */
    iteTerm[f]

  | /* Unary minus */
    MINUS_TOK unaryTerm[f] { f = MK_EXPR(CVC4::kind::UMINUS, f); }

  | /* parenthesized sub-formula */
    LPAREN formula[f] RPAREN

    /* constants */
  | TRUE_TOK  { f = MK_CONST(true); }
  | FALSE_TOK { f = MK_CONST(false); }

  | INTEGER_LITERAL { f = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) ); }
  | DECIMAL_LITERAL { f = MK_CONST( AntlrInput::tokenToRational($DECIMAL_LITERAL) ); }

  | /* variable */
    identifier[name,CHECK_DECLARED,SYM_VARIABLE]
    { f = PARSER_STATE->getVariable(name);
      // datatypes: 0-ary constructors
      if( PARSER_STATE->getType(name).isConstructor() ){
        args.push_back( f );
        f = MK_EXPR(CVC4::kind::APPLY_CONSTRUCTOR, args);
      }
    }
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
    { PARSER_STATE->checkFunctionLike(name);
      f = PARSER_STATE->getVariable(name); }
  ;

/**
 * Parses a datatype definition
 */
datatypeDef[std::vector<CVC4::Datatype>& datatypes]
@init {
  std::string id;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT]
    { datatypes.push_back(Datatype(id)); }
    EQUAL_TOK constructorDef[datatypes.back()]
    ( BAR_TOK constructorDef[datatypes.back()] )*
  ;

/**
 * Parses a constructor defintion for type
 */
constructorDef[CVC4::Datatype& type]
@init {
  std::string id;
  CVC4::Datatype::Constructor* ctor;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT]
    {
      // make the tester
      std::string testerId("is_");
      testerId.append(id);
      PARSER_STATE->checkDeclaration(testerId, CHECK_UNDECLARED, SYM_SORT);
      ctor = new CVC4::Datatype::Constructor(id, testerId);
    }
    ( LPAREN
      selector[*ctor]
      ( COMMA selector[*ctor] )*
      RPAREN
    )?
    { // make the constructor
      type.addConstructor(*ctor);
      Debug("parser-idt") << "constructor: " << id.c_str() << std::endl;
      delete ctor;
    }
  ;

selector[CVC4::Datatype::Constructor& ctor]
@init {
  std::string id;
  Type type;
}
  : identifier[id,CHECK_UNDECLARED,SYM_SORT] COLON maybeUndefinedBaseType[type,CHECK_NONE]
    { if(type.isNull()) {
        ctor.addArg(id, Datatype::UnresolvedType($maybeUndefinedBaseType.id));
      } else {
        ctor.addArg(id, type);
      }
      Debug("parser-idt") << "selector: " << id.c_str() << std::endl;
    }
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
IN_TOK : 'IN';
INT_TOK : 'INT';
LET_TOK : 'LET';
NOT_TOK : 'NOT';
OPTION_TOK : 'OPTION';
OR_TOK : 'OR';
POPTO_TOK : 'POPTO';
POP_TOK : 'POP';
PRINT_TOK : 'PRINT';
PUSH_TOK : 'PUSH';
QUERY_TOK : 'QUERY';
REAL_TOK : 'REAL';
THEN_TOK : 'THEN';
TRUE_TOK : 'TRUE';
TYPE_TOK : 'TYPE';
XOR_TOK : 'XOR';

DATATYPE_TOK : 'DATATYPE';
END_TOK : 'END';
BAR_TOK : '|';

ARRAY_TOK : 'ARRAY';
OF_TOK : 'OF';
WITH_TOK : 'WITH';

BITVECTOR_TOK : 'BITVECTOR';

// Symbols

COLON : ':';
COMMA : ',';
LPAREN : '(';
RPAREN : ')';
SEMICOLON : ';';

// Operators

ARROW_TOK : '->';
DIV_TOK : '/';
EQUAL_TOK : '=';
DISEQUAL_TOK : '/=';
EXP_TOK : '^';
GT_TOK : '>';
GEQ_TOK : '>=';
IFF_TOK : '<=>';
IMPLIES_TOK : '=>';
LT_TOK : '<';
LEQ_TOK : '<=';
MINUS_TOK : '-';
PLUS_TOK : '+';
STAR_TOK : '*';

/**
 * Matches an identifier from the input. An identifier is a sequence of letters,
 * digits and "_", "'", "." symbols, starting with a letter.
 */
IDENTIFIER : ALPHA (ALPHA | DIGIT | '_' | '\'' | '.')*;

/**
 * Matches an integer literal.
 */
INTEGER_LITERAL: DIGIT+;

/**
 * Matches a decimal literal.
 */
DECIMAL_LITERAL: DIGIT+ '.' DIGIT+;

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
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

/**
 * Matches and skips whitespace in the input and ignores it.
 */
WHITESPACE : (' ' | '\t' | '\f' | '\r' | '\n')+ { SKIP();; };

/**
 * Matches the comments and ignores them
 */
COMMENT : '%' (~('\n' | '\r'))* { SKIP();; };

/**
 * Matches an allowed escaped character.
 */
fragment ESCAPE : '\\' ('"' | '\\' | 'n' | 't' | 'r');


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

tokens {
  // Keywords

  AND_TOK = 'AND';
  ASSERT_TOK = 'ASSERT';
  BOOLEAN_TOK = 'BOOLEAN';
  CHECKSAT_TOK = 'CHECKSAT';
  ECHO_TOK = 'ECHO';
  ELSEIF_TOK = 'ELSIF';
  ELSE_TOK = 'ELSE';
  ENDIF_TOK = 'ENDIF';
  FALSE_TOK = 'FALSE';
  IF_TOK = 'IF';
  IN_TOK = 'IN';
  INT_TOK = 'INT';
  LET_TOK = 'LET';
  NOT_TOK = 'NOT';
  OPTION_TOK = 'OPTION';
  OR_TOK = 'OR';
  POPTO_TOK = 'POPTO';
  POP_TOK = 'POP';
  PRINT_TOK = 'PRINT';
  PUSH_TOK = 'PUSH';
  QUERY_TOK = 'QUERY';
  REAL_TOK = 'REAL';
  THEN_TOK = 'THEN';
  TRUE_TOK = 'TRUE';
  TYPE_TOK = 'TYPE';
  XOR_TOK = 'XOR';

  DATATYPE_TOK = 'DATATYPE';
  END_TOK = 'END';

  ARRAY_TOK = 'ARRAY';
  OF_TOK = 'OF';
  WITH_TOK = 'WITH';

  FORALL_TOK = 'FORALL';
  EXISTS_TOK = 'EXISTS';

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
  DOT = '.';

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

  //IS_INTEGER_TOK = 'IS_INTEGER';

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
  BVTOINT_TOK = 'BVTOINT';
  INTTOBV_TOK = 'INTTOBV';
  BOOLEXTRACT_TOK = 'BOOLEXTRACT';
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
}

@parser::members {

// Idea and code guidance from Sam Harwell,
// http://www.antlr.org/wiki/display/ANTLR3/Operator+precedence+parser

bool isRightToLeft(int type) {
  // return true here for any operators that are right-to-left associative
  switch(type) {
  case IMPLIES_TOK: return true;
  default: return false;
  }
}

int getOperatorPrecedence(int type) {
  switch(type) {
  case BITVECTOR_TOK: return 1;
  case DOT:
  case LPAREN:
  case LBRACE: return 2;
  case LBRACKET: return 3;
  case ARROW_TOK: return 4;
  //case IS_INTEGER_TOK: return 5;
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
  case MOD_TOK: return 23;
  case PLUS_TOK:
  case MINUS_TOK: return 24;
  case LEQ_TOK:
  case LT_TOK:
  case GEQ_TOK:
  case GT_TOK:
  case FLOOR_TOK: return 25;
  case EQUAL_TOK:
  case DISEQUAL_TOK: return 26;
  case NOT_TOK: return 27;
  case AND_TOK: return 28;
  case OR_TOK:
  case XOR_TOK: return 29;
  case IMPLIES_TOK: return 30;// right-to-left
  case IFF_TOK: return 31;
  case FORALL_TOK:
  case EXISTS_TOK: return 32;
  case ASSIGN_TOK:
  case IN_TOK: return 33;

  default:
    Unhandled(CvcParserTokenNames[type]);
  }
}

Kind getOperatorKind(int type, bool& negate) {
  negate = false;

  switch(type) {
    // booleanBinop
  case IFF_TOK: return kind::IFF;
  case IMPLIES_TOK: return kind::IMPLIES;
  case OR_TOK: return kind::OR;
  case XOR_TOK: return kind::XOR;
  case AND_TOK: return kind::AND;

    // comparisonBinop
  case EQUAL_TOK: return kind::EQUAL;
  case DISEQUAL_TOK: negate = true; return kind::EQUAL;
  case GT_TOK: return kind::GT;
  case GEQ_TOK: return kind::GEQ;
  case LT_TOK: return kind::LT;
  case LEQ_TOK: return kind::LEQ;

    // arithmeticBinop
  case PLUS_TOK: return kind::PLUS;
  case MINUS_TOK: return kind::MINUS;
  case STAR_TOK: return kind::MULT;
  case INTDIV_TOK: Unhandled(CvcParserTokenNames[type]);
  case DIV_TOK: return kind::DIVISION;
  case EXP_TOK: Unhandled(CvcParserTokenNames[type]);

    // concatBitwiseBinop
  case CONCAT_TOK: return kind::BITVECTOR_CONCAT;
  case BAR: return kind::BITVECTOR_OR;
  case BVAND_TOK: return kind::BITVECTOR_AND;

  default:
    Unhandled(CvcParserTokenNames[type]);
  }
}

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
}

Expr createPrecedenceTree(ExprManager* em,
                          const std::vector<CVC4::Expr>& expressions,
                          const std::vector<unsigned>& operators,
                          unsigned startIndex, unsigned stopIndex) {
  Assert(expressions.size() == operators.size() + 1);
  Assert(startIndex < expressions.size());
  Assert(stopIndex < expressions.size());
  Assert(startIndex <= stopIndex);

  if(stopIndex == startIndex) {
    return expressions[startIndex];
  }

  unsigned pivot = findPivot(operators, startIndex, stopIndex - 1);
  //Debug("prec") << "pivot[" << startIndex << "," << stopIndex - 1 << "] at " << pivot << std::endl;
  bool negate;
  Expr e = em->mkExpr(getOperatorKind(operators[pivot], negate),
                      createPrecedenceTree(em, expressions, operators, startIndex, pivot),
                      createPrecedenceTree(em, expressions, operators, pivot + 1, stopIndex));
  return negate ? em->mkExpr(kind::NOT, e) : e;
}

Expr createPrecedenceTree(ExprManager* em,
                          const std::vector<CVC4::Expr>& expressions,
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

  Expr e = createPrecedenceTree(em, expressions, operators, 0, expressions.size() - 1);
  if(Debug.isOn("prec") && operators.size() > 1) {
    Expr::setlanguage::Scope ls(Debug("prec"), language::output::LANG_AST);
    Debug("prec") << "=> " << e << std::endl;
  }
  return e;
}

}/* @parser::members */

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
    identifierList[ids, CHECK_UNDECLARED, SYM_VARIABLE] COLON declType[t, ids] SEMICOLON
    { cmd = new DeclarationCommand(ids, t); }
  ;

/** Match the right-hand side of a declaration. Returns the type. */
declType[CVC4::Type& t, std::vector<std::string>& idList]
@init {
  Expr f;
  Debug("parser-extra") << "declType: " << AntlrInput::tokenText(LT(1)) << std::endl;
}
  : /* A sort declaration (e.g., "T : TYPE") */
    TYPE_TOK
    { PARSER_STATE->mkSorts(idList);
      t = EXPR_MANAGER->kindType(); }
  | /* A type alias */
    TYPE_TOK EQUAL_TOK type[t]
    { for(std::vector<std::string>::const_iterator i = idList.begin();
          i != idList.end();
          ++i) {
        PARSER_STATE->defineType(*i, t);
      }
      t = EXPR_MANAGER->kindType(); }
  | /* A variable declaration */
    type[t] ( EQUAL_TOK formula[f] )?
    { if(f.isNull()) {
        PARSER_STATE->mkVars(idList, t);
      } else {
        for(std::vector<std::string>::const_iterator i = idList.begin(),
              i_end = idList.end();
            i != i_end;
            ++i) {
          PARSER_STATE->defineFunction(*i, f);
        }
      }
    }
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
    bitvectorType[t]
  | /* Single-parameter function type */
    baseType[t] ARROW_TOK baseType[t2]
    { t = EXPR_MANAGER->mkFunctionType(t, t2); }
  | /* Multi-parameter function type */
    LPAREN baseType[t]
    { typeList.push_back(t); }
    ( COMMA baseType[t] { typeList.push_back(t); } )*
    RPAREN ARROW_TOK baseType[t]
    { t = EXPR_MANAGER->mkFunctionType(typeList, t); }
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
 * Matches a bitvector type.
 */
bitvectorType[CVC4::Type& t]
  : arrayType[t]
  | BITVECTOR_TOK LPAREN INTEGER_LITERAL RPAREN
    { t = EXPR_MANAGER->mkBitVectorType(AntlrInput::tokenToUnsigned($INTEGER_LITERAL)); }
  ;

arrayType[CVC4::Type& t]
@init {
  Type t2;
}
  : baseType[t]
  | ARRAY_TOK baseType[t] OF_TOK baseType[t2]
    { t = EXPR_MANAGER->mkArrayType(t, t2); }
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
 * @return the type identifier in 't', and the id (where applicable) in 'id'
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
  | booleanFormula[f]
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

booleanFormula[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
  unsigned notCount = 0;
}
  : ( NOT_TOK { ++notCount; } )* comparison[f]
    { while(notCount > 0) {
        --notCount;
        f = EXPR_MANAGER->mkExpr(kind::NOT, f);
      }
      expressions.push_back(f); }
    ( booleanBinop[op] ( NOT_TOK { ++notCount; } )* comparison[f]
      { operators.push_back(op);
        while(notCount > 0) {
          --notCount;
          f = EXPR_MANAGER->mkExpr(kind::NOT, f);
        }
        expressions.push_back(f);
      }
    )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
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

comparison[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : term[f] { expressions.push_back(f); }
    ( comparisonBinop[op] term[f]
      { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
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
  ;

term[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : storeTerm[f] { expressions.push_back(f); }
    ( arithmeticBinop[op] storeTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
  ;

arithmeticBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : PLUS_TOK
  | MINUS_TOK
  | STAR_TOK
  | INTDIV_TOK
  | DIV_TOK
  | EXP_TOK
  ;

/** Parses an array store term. */
storeTerm[CVC4::Expr& f]
@init {
  Expr f2, f3;
}
  : uminusTerm[f] ( WITH_TOK
    LBRACKET formula[f2] RBRACKET ASSIGN_TOK uminusTerm[f3]
    { f = MK_EXPR(CVC4::kind::STORE, f, f2, f3); }
    ( COMMA LBRACKET formula[f2] RBRACKET ASSIGN_TOK uminusTerm[f3]
      { f = MK_EXPR(CVC4::kind::STORE, f, f2, f3); } )* )*
  ;

/** Parses a unary minus term. */
uminusTerm[CVC4::Expr& f]
@init {
  unsigned minusCount = 0;
}
  : /* Unary minus */
//    (MINUS_TOK { ++minusCount; })* concatBitwiseTerm[f]
    (MINUS_TOK { ++minusCount; })+ concatBitwiseTerm[f]
    { while(minusCount > 0) { --minusCount; f = MK_EXPR(CVC4::kind::UMINUS, f); } }
  | concatBitwiseTerm[f]
  ;

/** Parses bitvectors. */

concatBitwiseTerm[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : bitwiseXorTerm[f] { expressions.push_back(f); }
    ( concatBitwiseBinop[op] bitwiseXorTerm[f] { operators.push_back(op); expressions.push_back(f); } )*
    { f = createPrecedenceTree(EXPR_MANAGER, expressions, operators); }
  ;
concatBitwiseBinop[unsigned& op]
@init {
  op = LT(1)->getType(LT(1));
}
  : CONCAT_TOK
  | BAR
  | BVAND_TOK
  ;

bitwiseXorTerm[CVC4::Expr& f]
@init {
  Expr f2;
}
  : /* BV xor */
    BVXOR_TOK LPAREN formula[f] COMMA formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_XOR, f, f2); }
  | BVNAND_TOK LPAREN formula[f] COMMA formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NAND, f, f2); }
  | BVNOR_TOK LPAREN formula[f] COMMA formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NOR, f, f2); }
  | BVCOMP_TOK LPAREN formula[f] COMMA formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_COMP, f, f2); }
  | BVXNOR_TOK LPAREN formula[f] COMMA formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_XNOR, f, f2); }
  | bvNegTerm[f]
  ;
bvNegTerm[CVC4::Expr& f]
  : /* BV neg */
    BVNEG_TOK bvNegTerm[f]
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NOT, f); }
  | bvUminusTerm[f]
  ;
bvUminusTerm[CVC4::Expr& f]
@init {
  Expr f2;
}
  : /* BV unary minus */
    BVUMINUS_TOK LPAREN formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_NEG, f); }
  | BVPLUS_TOK LPAREN INTEGER_LITERAL COMMA formula[f]
    ( COMMA formula[f2] { f = MK_EXPR(CVC4::kind::BITVECTOR_PLUS, f, f2); } )+ RPAREN
    { unsigned size = BitVectorType(f.getType()).getSize();
      unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      if(k == 0) {
        PARSER_STATE->parseError("BVPLUS(k,_,_,...) must have k > 0");
      }
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(0, k - 1)), f);
      }
    }
  | BVSUB_TOK LPAREN INTEGER_LITERAL COMMA formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SUB, f, f2);
      unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      if(k == 0) {
        PARSER_STATE->parseError("BVSUB(k,_,_) must have k > 0");
      }
      unsigned size = BitVectorType(f.getType()).getSize();
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(0, k - 1)), f);
      }
    }
  | BVMULT_TOK LPAREN INTEGER_LITERAL COMMA formula[f] COMMA formula[f2] RPAREN
    { MK_EXPR(CVC4::kind::BITVECTOR_MULT, f, f2);
      unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      if(k == 0) {
        PARSER_STATE->parseError("BVMULT(k,_,_) must have k > 0");
      }
      unsigned size = BitVectorType(f.getType()).getSize();
      if(k > size) {
        f = MK_EXPR(MK_CONST(BitVectorZeroExtend(k)), f);
      } else if(k < size) {
        f = MK_EXPR(MK_CONST(BitVectorExtract(0, k - 1)), f);
      }
    }
  | BVUDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UDIV, f, f2); }
  | BVSDIV_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SDIV, f, f2); }
  | BVUREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UREM, f, f2); }
  | BVSREM_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SREM, f, f2); }
  | BVSMOD_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SMOD, f, f2); }
  | BVSHL_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SHL, f, f2); }
  | BVASHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ASHR, f, f2); }
  | BVLSHR_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_LSHR, f, f2); }
  | SX_TOK LPAREN formula[f] COMMA INTEGER_LITERAL RPAREN
    { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      f = MK_EXPR(MK_CONST(BitVectorSignExtend(k)), f); }
  | BVZEROEXTEND_TOK LPAREN formula[f] COMMA INTEGER_LITERAL RPAREN
    { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      f = MK_EXPR(MK_CONST(BitVectorSignExtend(k)), f); }
  | BVREPEAT_TOK LPAREN formula[f] COMMA INTEGER_LITERAL RPAREN
    { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      f = MK_EXPR(MK_CONST(BitVectorRepeat(k)), f); }
  | BVROTR_TOK LPAREN formula[f] COMMA INTEGER_LITERAL RPAREN
    { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      f = MK_EXPR(MK_CONST(BitVectorSignExtend(k)), f); }
  | BVROTL_TOK LPAREN formula[f] COMMA INTEGER_LITERAL RPAREN
    { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
      f = MK_EXPR(MK_CONST(BitVectorRotateLeft(k)), f); }
  | bvShiftTerm[f]
  ;

bvShiftTerm[CVC4::Expr& f]
@init {
  std::vector<CVC4::Expr> expressions;
  std::vector<unsigned> operators;
  unsigned op;
}
  : bvComparison[f]
    ( ( LEFTSHIFT_TOK | RIGHTSHIFT_TOK) INTEGER_LITERAL
      { unsigned k = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
        f = MK_EXPR(MK_CONST(BitVectorRotateLeft(k)), f); }
    )?
  ;

bvComparison[CVC4::Expr& f]
@init {
  Expr f2;
}
  : /* BV comparison */
    BVLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ULT, f, f2); }
  | BVLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_ULE, f, f2); }
  | BVGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UGT, f, f2); }
  | BVGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_UGE, f, f2); }
  | BVSLT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SLT, f, f2); }
  | BVSLE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SLE, f, f2); }
  | BVSGT_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SGT, f, f2); }
  | BVSGE_TOK LPAREN formula[f] COMMA formula[f2] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_SGE, f, f2); }
  /*
  | IS_INTEGER_TOK LPAREN formula[f] RPAREN
    { f = MK_EXPR(CVC4::kind::BITVECTOR_IS_INTEGER, f); }
  */
  | selectExtractTerm[f]
  ;

/** Parses an array select. */
selectExtractTerm[CVC4::Expr& f]
@init {
  Expr f2;
  bool extract;
}
  : /* array select / bitvector extract */
    simpleTerm[f]
    ( { extract = false; }
      LBRACKET formula[f2] ( COLON INTEGER_LITERAL { extract = true; } )? RBRACKET
      { if(extract) {
          if(f2.getKind() != kind::CONST_INTEGER) {
            PARSER_STATE->parseError("bitvector extraction requires [INTEGER_LITERAL:INTEGER_LITERAL] range");
          }
          unsigned k1 = f2.getConst<Integer>().getLong();
          unsigned k2 = AntlrInput::tokenToUnsigned($INTEGER_LITERAL);
          f = MK_EXPR(MK_CONST(BitVectorExtract(k1, k2)), f);
        } else {
          f = MK_EXPR(CVC4::kind::SELECT, f, f2);
        }
      }
    )*

  ;

/** Parses a simple term. */
simpleTerm[CVC4::Expr& f]
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

  | /* parenthesized sub-formula */
    LPAREN formula[f] RPAREN

    /* constants */
  | TRUE_TOK  { f = MK_CONST(true); }
  | FALSE_TOK { f = MK_CONST(false); }
  | INTEGER_LITERAL { f = MK_CONST( AntlrInput::tokenToInteger($INTEGER_LITERAL) ); }
  | DECIMAL_LITERAL { f = MK_CONST( AntlrInput::tokenToRational($DECIMAL_LITERAL) ); }
  | HEX_LITERAL
    { Assert( AntlrInput::tokenText($HEX_LITERAL).find("0hex") == 0 );
      std::string hexString = AntlrInput::tokenTextSubstr($HEX_LITERAL, 4);
      f = MK_CONST( BitVector(hexString, 16) ); }
  | BINARY_LITERAL
    { Assert( AntlrInput::tokenText($BINARY_LITERAL).find("0bin") == 0 );
      std::string binString = AntlrInput::tokenTextSubstr($BINARY_LITERAL, 4);
      f = MK_CONST( BitVector(binString, 2) ); }

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
    ( BAR constructorDef[datatypes.back()] )*
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
  : identifier[id,CHECK_UNDECLARED,SYM_SORT] COLON
    maybeUndefinedBaseType[type,CHECK_NONE]
    // TODO: this doesn't permit datatype fields of ARRAY or BITVECTOR
    // type.  This will be problematic, since, after all, you could
    // have something nasty like this:
    //
    //   DATATYPE list = cons(car:ARRAY list OF list, cdr:list) | nil END;
    { if(type.isNull()) {
        ctor.addArg(id, Datatype::UnresolvedType($maybeUndefinedBaseType.id));
      } else {
        ctor.addArg(id, type);
      }
      Debug("parser-idt") << "selector: " << id.c_str() << std::endl;
    }
  ;

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
 * Matches the digits (0-9)
 */
fragment DIGIT : '0'..'9';

fragment HEX_DIGIT : DIGIT | 'a'..'f' | 'A'..'F';

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


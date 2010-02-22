/* *******************                                                        */
/*  cvc_parser.g
 ** Original author: dejan
 ** Major contributors: cconway
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Parser for CVC presentation language.
 **/

header "post_include_hpp" {
#include "parser/antlr_parser.h"
#include "expr/command.h"
#include "expr/type.h"
#include "util/output.h"
}

header "post_include_cpp" {
#include <vector>

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
}

options {
  language = "Cpp";                  // C++ output for antlr
  namespaceStd = "std";              // Cosmetic option to get rid of long defines in generated code
  namespaceAntlr = "antlr";          // Cosmetic option to get rid of long defines in generated code
  namespace = "CVC4::parser";        // Wrap everything in the smtparser namespace
}

/**
 * AntlrCvcParser class is the parser for the files in CVC format.
 */
class AntlrCvcParser extends Parser("AntlrParser");
options {
  genHashLines = true;              // Include line number information
  importVocab = CvcVocabulary;      // Import the common vocabulary
  defaultErrorHandler = false;      // Skip the defaul error handling, just break with exceptions
  k = 2;
}

/**
 * Parses the next command.
 * @return command or 0 if EOF
 */
parseCommand returns [CVC4::Command* cmd]
  : cmd = command
  ;

/**
 * Parses the next expression.
 * @return the parsed expression (null expression if EOF)
 */
parseExpr returns [CVC4::Expr expr]
  : expr = formula
  | EOF
  ;

/**
 * Matches a command of the input. If a declaration, it will return an empty
 * command.
 */
command returns [CVC4::Command* cmd = 0]
{
  Expr f;
  Debug("parser") << "command: " << LT(1)->getText() << endl;
}
  : ASSERT   f = formula  SEMICOLON { cmd = new AssertCommand(f);   }
  | QUERY    f = formula  SEMICOLON { cmd = new QueryCommand(f);    }
  | CHECKSAT f = formula  SEMICOLON { cmd = new CheckSatCommand(f); }
  | CHECKSAT              SEMICOLON { cmd = new CheckSatCommand(getTrueExpr()); }
  | PUSH                  SEMICOLON { cmd = new PushCommand(); }
  | POP                   SEMICOLON { cmd = new PopCommand(); }
  | cmd = declaration
  | EOF
  ;

/**
 * Match a declaration
 */

declaration returns [CVC4::DeclarationCommand* cmd]
{
  vector<string> ids;
  const Type* t;
  Debug("parser") << "declaration: " << LT(1)->getText() << endl;
} 
  : identifierList[ids, CHECK_UNDECLARED] COLON t = declType[ids] SEMICOLON
    { cmd = new DeclarationCommand(ids,t); }
  ;

/** Match the right-hand side of a declaration. Returns the type. */
declType[std::vector<std::string>& idList] returns [const CVC4::Type* t]
{
  Debug("parser") << "declType: " << LT(1)->getText() << endl;
}
  : /* A sort declaration (e.g., "T : TYPE") */
    TYPE { newSorts(idList); t = kindType(); }
  | /* A variable declaration */
    t = type { mkVars(idList,t); }
  ;

/**
 * Match the type in a declaration and do the declaration binding.
 * TODO: Actually parse sorts into Type objects.
 */
type returns  [const CVC4::Type* t]
{
  const Type *t1, *t2;
  Debug("parser") << "type: " << LT(1)->getText() << endl;
}
  : /* Simple type */
    t = baseType
  | /* Single-parameter function type */
    t1 = baseType RIGHT_ARROW t2 = baseType
    { t = functionType(t1,t2); }
  | /* Multi-parameter function type */
    LPAREN t1 = baseType 
    { std::vector<const Type*> argTypes;
      argTypes.push_back(t1); }
    (COMMA t1 = baseType { argTypes.push_back(t1); } )+ 
    RPAREN RIGHT_ARROW t2 = baseType
    { t = functionType(argTypes,t2); }
  ;

/**
 * Matches a list of identifiers separated by a comma and puts them in the
 * given list.
 * @param idList the list to fill with identifiers.
 * @param check what kinds of check to perform on the symbols
 */
identifierList[std::vector<std::string>& idList, 
               DeclarationCheck check = CHECK_NONE]
{
  string id;
}
  : id = identifier[check] { idList.push_back(id); }
      (COMMA id = identifier[check] { idList.push_back(id); })*
  ;


/**
 * Matches an identifier and returns a string.
 */
identifier[DeclarationCheck check = CHECK_NONE,
           SymbolType type = SYM_VARIABLE] 
returns [std::string id]
  : x:IDENTIFIER
    { id = x->getText(); 
      checkDeclaration(id, check, type); }
  ;

/**
 * Matches a type.
 * TODO: parse more types
 */
baseType returns [const CVC4::Type* t]
{
  std::string id;
  Debug("parser") << "base type: " << LT(1)->getText() << endl;
}
  : BOOLEAN { t = booleanType(); }
  | t = typeSymbol
  ;

/**
 * Matches a type identifier
 */
typeSymbol returns [const CVC4::Type* t]
{
  std::string id;
  Debug("parser") << "type symbol: " << LT(1)->getText() << endl;
}
  : id = identifier[CHECK_DECLARED,SYM_SORT]
    { t = getSort(id); }
  ;

/**
 * Matches a CVC4 formula.
 * @return the expression representing the formula
 */
formula returns [CVC4::Expr formula]
{
  Debug("parser") << "formula: " << LT(1)->getText() << endl;
}
  :  formula = iffFormula
  ;

/**
 * Matches a comma-separated list of formulas
 */
formulaList[std::vector<CVC4::Expr>& formulas]
{
  Expr f;
}
  : f = formula { formulas.push_back(f); }
    ( COMMA f = formula
      { formulas.push_back(f); }
    )*
  ;

/**
 * Matches a Boolean IFF formula (right-associative)
 */
iffFormula returns [CVC4::Expr f]
{
  Expr e;
  Debug("parser") << "<=> formula: " << LT(1)->getText() << endl;
}
  : f = impliesFormula
    ( IFF e = iffFormula
        { f = mkExpr(CVC4::IFF, f, e); }
    )?
  ;

/**
 * Matches a Boolean IMPLIES formula (right-associative)
 */
impliesFormula returns [CVC4::Expr f]
{
  Expr e;
  Debug("parser") << "=> Formula: " << LT(1)->getText() << endl;
}
  : f = orFormula 
    ( IMPLIES e = impliesFormula
        { f = mkExpr(CVC4::IMPLIES, f, e); }
    )?
  ;

/**
 * Matches a Boolean OR formula (left-associative)
 */
orFormula returns [CVC4::Expr f]
{
  Expr e;
  vector<Expr> exprs;
  Debug("parser") << "OR Formula: " << LT(1)->getText() << endl;
}
  : e = xorFormula { exprs.push_back(e); }
      ( OR e = xorFormula { exprs.push_back(e); } )*
    {
      f = (exprs.size() > 1 ? mkExpr(CVC4::OR, exprs) : exprs[0]);
    }
  ;

/**
 * Matches a Boolean XOR formula (left-associative)
 */
xorFormula returns [CVC4::Expr f]
{
  Expr e;
  Debug("parser") << "XOR formula: " << LT(1)->getText() << endl;
}
  : f = andFormula
    ( XOR e = andFormula 
      { f = mkExpr(CVC4::XOR,f, e); }
    )*
  ;

/**
 * Matches a Boolean AND formula (left-associative)
 */
andFormula returns [CVC4::Expr f]
{
  Expr e;
  vector<Expr> exprs;
  Debug("parser") << "AND Formula: " << LT(1)->getText() << endl;
}
  : e = notFormula { exprs.push_back(e); }
    ( AND e = notFormula { exprs.push_back(e); } )*
    {
      f = (exprs.size() > 1 ? mkExpr(CVC4::AND, exprs) : exprs[0]);
    }
  ;

/**
 * Parses a NOT formula.
 * @return the expression representing the formula
 */
notFormula returns [CVC4::Expr f]
{
  Debug("parser") << "NOT formula: " << LT(1)->getText() << endl;
}
  : /* negation */
    NOT f = notFormula 
    { f = mkExpr(CVC4::NOT, f); }
  | /* a boolean atom */
    f = predFormula
  ;

predFormula returns [CVC4::Expr f]
{
  Debug("parser") << "predicate formula: " << LT(1)->getText() << endl;
}
  : { Expr e; }
    f = term 
    (EQUAL e = term
      { f = mkExpr(CVC4::EQUAL, f, e); }
    )?
  ; // TODO: lt, gt, etc.

/**
 * Parses a term.
 */
term returns [CVC4::Expr t]
{
  std::string name;
  Debug("parser") << "term: " << LT(1)->getText() << endl;
}
  : /* function application */
    // { isFunction(LT(1)->getText()) }? 
    { Expr f; 
      std::vector<CVC4::Expr> args; }
    f = functionSymbol[CHECK_DECLARED]
    { args.push_back( f ); }

    LPAREN formulaList[args] RPAREN
    // TODO: check arity
    { t = mkExpr(CVC4::APPLY, args); }

  | /* if-then-else */
    t = iteTerm

  | /* parenthesized sub-formula */
    LPAREN t = formula RPAREN

    /* constants */
  | TRUE  { t = getTrueExpr(); }
  | FALSE { t = getFalseExpr(); }

  | /* variable */
    name = identifier[CHECK_DECLARED]
    { t = getVariable(name); }
  ;

/**
 * Parses an ITE term.
 */
iteTerm returns [CVC4::Expr t] 
{
  Expr iteCondition, iteThen, iteElse;
  Debug("parser") << "ite: " << LT(1)->getText() << endl;
}
  : IF iteCondition = formula 
    THEN iteThen = formula
    iteElse = iteElseTerm
    ENDIF     
    { t = mkExpr(CVC4::ITE, iteCondition, iteThen, iteElse); }  
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseTerm returns [CVC4::Expr t]
{
  Expr iteCondition, iteThen, iteElse;
  Debug("parser") << "else: " << LT(1)->getText() << endl;
}
  : ELSE t = formula
  | ELSEIF iteCondition = formula
    THEN iteThen = formula
    iteElse = iteElseTerm
    { t = mkExpr(CVC4::ITE, iteCondition, iteThen, iteElse); }
  ;

/**
 * Parses a function symbol (an identifier).
 * @param what kind of check to perform on the id
 * @return the predicate symol
 */
functionSymbol[DeclarationCheck check = CHECK_NONE] returns [CVC4::Expr f]
{
  Debug("parser") << "function symbol: " << LT(1)->getText() << endl;
  std::string name;
}  
  : name = identifier[check,SYM_FUNCTION]
    { checkFunction(name);  
      f = getFunction(name); }
  ;

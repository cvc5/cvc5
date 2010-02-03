/* cvc_parser.g
 * Original author: dejan
 * Major contributors:
 * Minor contributors (to current version): none
 * This file is part of the CVC4 prototype.
 * Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 * Courant Institute of Mathematical Sciences
 * New York University
 * See the file COPYING in the top-level source directory for licensing
 * information.
 *
 * Parser for CVC presentation language.
 */

header "post_include_hpp" {
#include "parser/antlr_parser.h"
#include "util/command.h"
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
  vector<string> ids;
}
  : ASSERT   f = formula  SEMICOLON { cmd = new AssertCommand(f);   }
  | QUERY    f = formula  SEMICOLON { cmd = new QueryCommand(f);    }
  | CHECKSAT f = formula  SEMICOLON { cmd = new CheckSatCommand(f); }
  | CHECKSAT              SEMICOLON { cmd = new CheckSatCommand();  }
  | identifierList[ids, CHECK_UNDECLARED] COLON type {
      // FIXME: switch on type (may not be predicates)
      vector<string> sorts;
      newPredicates(ids,sorts);
      cmd = new DeclarationCommand(ids);
    }
    SEMICOLON
  | EOF
  ;

/**
 * Mathches a list of identifiers separated by a comma and puts them in the
 * given list.
 * @param idList the list to fill with identifiers.
 * @param check what kinds of check to perform on the symbols
 */
identifierList[std::vector<std::string>& idList, DeclarationCheck check = CHECK_NONE]
{
  string id;
}
  : id = identifier[check] { idList.push_back(id); }
      (COMMA id = identifier[check] { idList.push_back(id); })*
  ;


/**
 * Matches an identifier and returns a string.
 */
identifier[DeclarationCheck check = CHECK_NONE] returns [std::string id]
  : x:IDENTIFIER
    { id = x->getText(); }
    { checkDeclaration(id, check) }?
    exception catch [antlr::SemanticException& ex] {
      switch (check) {
        case CHECK_DECLARED: rethrow(ex, "Symbol " + id + " not declared");
        case CHECK_UNDECLARED: rethrow(ex, "Symbol " + id + " already declared");
        default: throw ex;
      }
    }
  ;

/**
 * Matches a type.
 * TODO: parse more types
 */
type
  : BOOLEAN
  ;

/**
 * Matches a CVC4 formula.
 * @return the expression representing the formula
 */
formula returns [CVC4::Expr formula]
  :  formula = boolFormula
  ;

/**
 * Matches a CVC4 basic Boolean formula (AND, OR, NOT...). It parses the list of
 * operands (primaryBoolFormulas) and operators (Kinds) and then calls the
 * createPrecedenceExpr method to build the expression using the precedence
 * and associativity of the operators.
 * @return the expression representing the formula
 */
boolFormula returns [CVC4::Expr formula]
  : formula = boolAndFormula
  ;

/**
 * Matches a Boolean AND formula of a given kind by doing a recursive descent.
 */
boolAndFormula returns [CVC4::Expr andFormula]
{
  Expr e;
  vector<Expr> exprs;
}
  : e = boolXorFormula { exprs.push_back(e); }
      ( AND e = boolXorFormula { exprs.push_back(e); } )*
    {
      andFormula = (exprs.size() > 1 ? mkExpr(CVC4::AND, exprs) : exprs[0]);
    }
  ;

/**
 * Matches a Boolean XOR formula of a given kind by doing a recursive descent.
 */
boolXorFormula returns [CVC4::Expr xorFormula]
{
  Expr e;
  vector<Expr> exprs;
}
  : e = boolOrFormula { exprs.push_back(e); }
      ( XOR e = boolOrFormula { exprs.push_back(e); } )*
    {
      xorFormula = (exprs.size() > 1 ? mkExpr(CVC4::XOR, exprs) : exprs[0]);
    }
  ;

/**
 * Matches a Boolean OR formula of a given kind by doing a recursive descent.
 */
boolOrFormula returns [CVC4::Expr orFormula]
{
  Expr e;
  vector<Expr> exprs;
}
  : e = boolImpliesFormula { exprs.push_back(e); }
      ( OR e = boolImpliesFormula { exprs.push_back(e); } )*
    {
      orFormula = (exprs.size() > 1 ? mkExpr(CVC4::OR, exprs) : exprs[0]);
    }
  ;

/**
 * Matches a Boolean IMPLIES formula of a given kind by doing a recursive descent.
 */
boolImpliesFormula returns [CVC4::Expr impliesFormula]
{
  vector<Expr> exprs;
  Expr e;
}
  : e = boolIffFormula { exprs.push_back(e); }
    ( IMPLIES e = boolIffFormula { exprs.push_back(e); }
    )*
    {
      impliesFormula = exprs.back();
      for (int i = exprs.size() - 2; i >= 0; -- i) {
        impliesFormula = mkExpr(CVC4::IMPLIES, exprs[i], impliesFormula);
      }
    }
  ;

/**
 * Matches a Boolean IFF formula of a given kind by doing a recursive descent.
 */
boolIffFormula returns [CVC4::Expr iffFormula]
{
  Expr e;
}
  : iffFormula = primaryBoolFormula
    ( IFF e = primaryBoolFormula
        { iffFormula = mkExpr(CVC4::IFF, iffFormula, e); }
    )*
  ;

/**
 * Parses a primary Boolean formula. A primary Boolean formula is either a
 * Boolean atom (variables and predicates) a negation of a primary Boolean
 * formula or a formula enclosed in parenthesis.
 * @return the expression representing the formula
 */
primaryBoolFormula returns [CVC4::Expr formula]
  : formula = boolAtom
  | formula = iteFormula
  | NOT formula = primaryBoolFormula { formula = mkExpr(CVC4::NOT, formula); }
  | LPAREN formula = boolFormula RPAREN
  ;

/**
 * Parses an ITE boolean formula.
 */
iteFormula returns [CVC4::Expr formula] 
{
  Expr iteCondition, iteThen, iteElse;
}
  : IF iteCondition = boolFormula 
    THEN iteThen = boolFormula
    iteElse = iteElseFormula
    ENDIF     
    { formula = mkExpr(CVC4::ITE, iteCondition, iteThen, iteElse); }  
  ;

/**
 * Parses the else part of the ITE, i.e. ELSE f, or ELSIF b THEN f1 ...
 */
iteElseFormula returns [CVC4::Expr formula]
{
  Expr iteCondition, iteThen, iteElse;
}
  : ELSE formula = boolFormula
  | ELSEIF iteCondition = boolFormula
    THEN iteThen = boolFormula
    iteElse = iteElseFormula
    { formula = mkExpr(CVC4::ITE, iteCondition, iteThen, iteElse); }
  ;

/**
 * Parses the Boolean atoms (variables and predicates).
 * @return the expression representing the atom.
 */
boolAtom returns [CVC4::Expr atom]
{
  string p;
}
  : p = predicateSymbol[CHECK_DECLARED] { atom = getVariable(p); }
      exception catch [antlr::SemanticException ex] {
        rethrow(ex, "Undeclared variable " + p);
      }
  | TRUE  { atom = getTrueExpr(); }
  | FALSE { atom = getFalseExpr(); }
  ;

/**
 * Parses a predicate symbol (an identifier).
 * @param what kind of check to perform on the id
 * @return the predicate symol
 */
predicateSymbol[DeclarationCheck check = CHECK_NONE] returns [std::string pSymbol]
  : pSymbol = identifier[check]
  ;

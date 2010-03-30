/*********************                                                        */
/** antlr_parser.cpp
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
 ** A super-class for ANTLR-generated input language parsers
 **/

/*
 * antlr_parser.cpp
 *
 *  Created on: Nov 30, 2009
 *      Author: dejan
 */

#include <iostream>
#include <limits.h>

#include "antlr_parser.h"
#include "util/output.h"
#include "util/Assert.h"
#include "expr/command.h"
#include "expr/type.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::parser;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

AntlrParser::AntlrParser(const antlr::ParserSharedInputState& state, int k) :
  antlr::LLkParser(state, k), d_checksEnabled(true) {
}

AntlrParser::AntlrParser(antlr::TokenBuffer& tokenBuf, int k) :
  antlr::LLkParser(tokenBuf, k), d_checksEnabled(true) {
}

AntlrParser::AntlrParser(antlr::TokenStream& lexer, int k) :
  antlr::LLkParser(lexer, k), d_checksEnabled(true) {
}

Expr AntlrParser::getSymbol(const std::string& name, SymbolType type) {
  Assert( isDeclared(name, type) );


  switch( type ) {

  case SYM_VARIABLE: // Functions share var namespace
  case SYM_FUNCTION:
    return d_varSymbolTable.getObject(name);

  default:
    Unhandled(type);
  }
}

Expr AntlrParser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Expr AntlrParser::getFunction(const std::string& name) {
  return getSymbol(name, SYM_FUNCTION);
}

Type* AntlrParser::getType(const std::string& var_name,
                           SymbolType type) {
  Assert( isDeclared(var_name, type) );
  Type* t = getSymbol(var_name, type).getType();
  return t;
}

Type* AntlrParser::getSort(const std::string& name) {
  Assert( isDeclared(name, SYM_SORT) );
  Type* t = d_sortTable.getObject(name);
  return t;
}

/* Returns true if name is bound to a boolean variable. */
bool AntlrParser::isBoolean(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name)->isBoolean();
}

/* Returns true if name is bound to a function. */
bool AntlrParser::isFunction(const std::string& name) {
  return isDeclared(name, SYM_FUNCTION) && getType(name)->isFunction();
}

/* Returns true if name is bound to a function returning boolean. */
bool AntlrParser::isPredicate(const std::string& name) {
  return isDeclared(name, SYM_FUNCTION) && getType(name)->isPredicate();
}

Expr AntlrParser::getTrueExpr() const {
  return d_exprManager->mkExpr(TRUE);
}

Expr AntlrParser::getFalseExpr() const {
  return d_exprManager->mkExpr(FALSE);
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child) {
  Expr result = d_exprManager->mkExpr(kind, child);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child_1, const Expr& child_2) {
  Expr result = d_exprManager->mkExpr(kind, child_1, child_2);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const Expr& child_1, const Expr& child_2,
                         const Expr& child_3) {
  Expr result = d_exprManager->mkExpr(kind, child_1, child_2, child_3);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Expr AntlrParser::mkExpr(Kind kind, const std::vector<Expr>& children) {
  Expr result = d_exprManager->mkExpr(kind, children);
  Debug("parser") << "mkExpr() => " << result << std::endl;
  return result;
}

Type* AntlrParser::functionType(Type* domainType,
                                Type* rangeType) {
  return d_exprManager->mkFunctionType(domainType, rangeType);
}

Type* AntlrParser::functionType(const std::vector<Type*>& argTypes,
                                Type* rangeType) {
  Assert( argTypes.size() > 0 );
  return d_exprManager->mkFunctionType(argTypes, rangeType);
}

Type* AntlrParser::functionType(const std::vector<Type*>& sorts) {
  Assert( sorts.size() > 0 );
  if( sorts.size() == 1 ) {
    return sorts[0];
  } else {
    std::vector<Type*> argTypes(sorts);
    Type* rangeType = argTypes.back();
    argTypes.pop_back();
    return functionType(argTypes, rangeType);
  }
}

Type* AntlrParser::predicateType(const std::vector<Type*>& sorts) {
  if(sorts.size() == 0) {
    return d_exprManager->booleanType();
  } else {
    return d_exprManager->mkFunctionType(sorts, d_exprManager->booleanType());
  }
}

Expr AntlrParser::mkVar(const std::string& name, Type* type) {
  Debug("parser") << "mkVar(" << name << "," << *type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(type, name);
  defineVar(name, expr);
  return expr;
}

const std::vector<Expr>
AntlrParser::mkVars(const std::vector<std::string> names,
                    Type* type) {
  std::vector<Expr> vars;
  for(unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type));
  }
  return vars;
}

void AntlrParser::defineVar(const std::string& name, const Expr& val) {
  Assert(!isDeclared(name));
  d_varSymbolTable.bindName(name, val);
  Assert(isDeclared(name));
}

void AntlrParser::undefineVar(const std::string& name) {
  Assert(isDeclared(name));
  d_varSymbolTable.unbindName(name);
  Assert(!isDeclared(name));
}


Type* AntlrParser::newSort(const std::string& name) {
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  Assert( !isDeclared(name, SYM_SORT) );
  Type* type = d_exprManager->mkSort(name);
  d_sortTable.bindName(name, type);
  Assert( isDeclared(name, SYM_SORT) );
  return type;
}

const std::vector<Type*>
AntlrParser::newSorts(const std::vector<std::string>& names) {
  std::vector<Type*> types;
  for(unsigned i = 0; i < names.size(); ++i) {
    types.push_back(newSort(names[i]));
  }
  return types;
}

void AntlrParser::setLogic(const std::string& name) {
  if( name == "QF_UF" ) {
    newSort("U");
  } else {
    Unhandled(name);
  }
}

BooleanType* AntlrParser::booleanType() {
  return d_exprManager->booleanType();
}

KindType* AntlrParser::kindType() {
  return d_exprManager->kindType();
}

unsigned int AntlrParser::minArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case AND:
  case NOT:
  case OR:
    return 1;

  case APPLY_UF:
  case EQUAL:
  case IFF:
  case IMPLIES:
  case PLUS:
  case XOR:
    return 2;

  case ITE:
    return 3;

  default:
    Unhandled(kind);
  }
}

unsigned int AntlrParser::maxArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case NOT:
    return 1;

  case EQUAL:
  case IFF:
  case IMPLIES:
  case XOR:
    return 2;

  case ITE:
    return 3;

  case AND:
  case APPLY_UF:
  case PLUS:
  case OR:
    return UINT_MAX;

  default:
    Unhandled(kind);
  }
}

void AntlrParser::setExpressionManager(ExprManager* em) {
  d_exprManager = em;
}

bool AntlrParser::isDeclared(const std::string& name, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE: // Functions share var namespace
  case SYM_FUNCTION:
    return d_varSymbolTable.isBound(name);
  case SYM_SORT:
    return d_sortTable.isBound(name);
  default:
    Unhandled(type);
  }
}

void AntlrParser::parseError(const std::string& message)
    throw (antlr::SemanticException) {
  throw antlr::SemanticException(message, getFilename(),
                                 LT(1).get()->getLine(),
                                 LT(1).get()->getColumn());
}

void AntlrParser::checkDeclaration(const std::string& varName,
                                   DeclarationCheck check,
                                   SymbolType type)
    throw (antlr::SemanticException) {
  if(!d_checksEnabled) {
    return;
  }

  switch(check) {
  case CHECK_DECLARED:
    if( !isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " not declared");
    }
    break;

  case CHECK_UNDECLARED:
    if( isDeclared(varName, type) ) {
      parseError("Symbol " + varName + " previously declared");
    }
    break;

  case CHECK_NONE:
    break;

  default:
    Unhandled(check);
  }
}

void AntlrParser::checkFunction(const std::string& name)
  throw (antlr::SemanticException) {
  if( d_checksEnabled && !isFunction(name) ) {
    parseError("Expecting function symbol, found '" + name + "'");
  }
}

void AntlrParser::checkArity(Kind kind, unsigned int numArgs)
  throw (antlr::SemanticException) {
  if(!d_checksEnabled) {
    return;
  }

  unsigned int min = minArity(kind);
  unsigned int max = maxArity(kind);

  if( numArgs < min || numArgs > max ) {
    stringstream ss;
    ss << "Expecting ";
    if( numArgs < min ) {
      ss << "at least " << min << " ";
    } else {
      ss << "at most " << max << " ";
    }
    ss << "arguments for operator '" << kind << "', ";
    ss << "found " << numArgs;
    parseError(ss.str());
  }
}

void AntlrParser::enableChecks() {
  d_checksEnabled = true;
}

void AntlrParser::disableChecks() {
  d_checksEnabled = false;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

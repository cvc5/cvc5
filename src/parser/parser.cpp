/*********************                                                        */
/*! \file parser.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, cconway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Parser state implementation.
 **
 ** Parser state implementation.
 **/

#include <iostream>
#include <fstream>
#include <stdint.h>

#include "input.h"
#include "parser.h"
#include "parser_exception.h"
#include "expr/command.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "util/output.h"
#include "util/Assert.h"
#include "parser/cvc/cvc_input.h"
#include "parser/smt/smt_input.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* exprManager, Input* input, bool strictMode) :
  d_exprManager(exprManager),
  d_input(input),
  d_done(false),
  d_checksEnabled(true),
  d_strictMode(strictMode) {
  d_input->setParser(*this);
}

Expr Parser::getSymbol(const std::string& name, SymbolType type) {
  Assert( isDeclared(name, type) );

  switch( type ) {

  case SYM_VARIABLE: // Functions share var namespace
    return d_declScope.lookup(name);

  default:
    Unhandled(type);
  }
}


Expr Parser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Type
Parser::getType(const std::string& var_name,
                     SymbolType type) {
  Assert( isDeclared(var_name, type) );
  Type t = getSymbol(var_name,type).getType();
  return t;
}

Type Parser::getSort(const std::string& name) {
  Assert( isDeclared(name, SYM_SORT) );
  Type t = d_declScope.lookupType(name);
  return t;
}

/* Returns true if name is bound to a boolean variable. */
bool Parser::isBoolean(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isBoolean();
}

/* Returns true if name is bound to a function. */
bool Parser::isFunction(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isFunction();
}

/* Returns true if name is bound to a function returning boolean. */
bool Parser::isPredicate(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isPredicate();
}

Expr 
Parser::mkVar(const std::string& name, const Type& type) {
  Debug("parser") << "mkVar(" << name << "," << type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(name, type);
  defineVar(name,expr);
  return expr;
}

const std::vector<Expr>
Parser::mkVars(const std::vector<std::string> names,
                    const Type& type) {
  std::vector<Expr> vars;
  for(unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i],type));
  }
  return vars;
}

void
Parser::defineVar(const std::string& name, const Expr& val) {
  d_declScope.bind(name,val);
  Assert(isDeclared(name));
}

void
Parser::defineType(const std::string& name, const Type& type) {
  d_declScope.bindType(name,type);
  Assert( isDeclared(name, SYM_SORT) ) ;
}

Type
Parser::mkSort(const std::string& name) {
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  Type type = d_exprManager->mkSort(name);
  defineType(name,type);
  return type;
}

const std::vector<Type>
Parser::mkSorts(const std::vector<std::string>& names) {
  std::vector<Type> types;
  for(unsigned i = 0; i < names.size(); ++i) {
    types.push_back(mkSort(names[i]));
  }
  return types;
}

bool Parser::isDeclared(const std::string& name, SymbolType type) {
  switch(type) {
  case SYM_VARIABLE:
    return d_declScope.isBound(name);
  case SYM_SORT:
    return d_declScope.isBoundType(name);
  default:
    Unhandled(type);
  }
}

void Parser::checkDeclaration(const std::string& varName,
                                   DeclarationCheck check,
                                   SymbolType type)
    throw (ParserException) {
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

void Parser::checkFunction(const std::string& name)
  throw (ParserException) {
  if( d_checksEnabled && !isFunction(name) ) {
    parseError("Expecting function symbol, found '" + name + "'");
  }
}

void Parser::checkArity(Kind kind, unsigned int numArgs)
  throw (ParserException) {
  if(!d_checksEnabled) {
    return;
  }

  unsigned int min = d_exprManager->minArity(kind);
  unsigned int max = d_exprManager->maxArity(kind);

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

void Parser::checkOperator(Kind kind, unsigned int numArgs) throw (ParserException) {
  if( d_strictMode && d_logicOperators.find(kind) == d_logicOperators.end() ) {
    parseError( "Operator is not defined in the current logic: " + kindToString(kind) );
  }
  checkArity(kind,numArgs);
}

void Parser::addOperator(Kind kind) {
  d_logicOperators.insert(kind);
}

Command* Parser::nextCommand() throw(ParserException) {
  Debug("parser") << "nextCommand()" << std::endl;
  Command* cmd = NULL;
  if(!done()) {
    try {
      cmd = d_input->parseCommand();
      if(cmd == NULL) {
        setDone();
      }
    } catch(ParserException& e) {
      setDone();
      throw;
    }
  }
  Debug("parser") << "nextCommand() => " << cmd << std::endl;
  return cmd;
}

Expr Parser::nextExpression() throw(ParserException) {
  Debug("parser") << "nextExpression()" << std::endl;
  Expr result;
  if(!done()) {
    try {
      result = d_input->parseExpr();
      if(result.isNull()) {
        setDone();
      }
    } catch(ParserException& e) {
      setDone();
      throw;
    }
  }
  Debug("parser") << "nextExpression() => " << result << std::endl;
  return result;
}


}/* CVC4::parser namespace */
}/* CVC4 namespace */

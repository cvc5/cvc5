/*********************                                                        */
/*! \file parser.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Parser state implementation.
 **
 ** Parser state implementation.
 **/

#include "parser/parser.h"

#include <stdint.h>

#include <cassert>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>

#include "base/output.h"
#include "expr/expr.h"
#include "expr/expr_iomanip.h"
#include "expr/kind.h"
#include "expr/type.h"
#include "options/options.h"
#include "parser/input.h"
#include "parser/parser_exception.h"
#include "smt/command.h"
#include "util/resource_manager.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace parser {

Parser::Parser(ExprManager* exprManager, Input* input, bool strictMode,
               bool parseOnly)
    : d_exprManager(exprManager),
      d_resourceManager(d_exprManager->getResourceManager()),
      d_input(input),
      d_symtabAllocated(),
      d_symtab(&d_symtabAllocated),
      d_assertionLevel(0),
      d_globalDeclarations(false),
      d_anonymousFunctionCount(0),
      d_done(false),
      d_checksEnabled(true),
      d_strictMode(strictMode),
      d_parseOnly(parseOnly),
      d_canIncludeFile(true),
      d_logicIsForced(false),
      d_forcedLogic() {
  d_input->setParser(*this);
}

Parser::~Parser() {
  for (std::list<Command*>::iterator iter = d_commandQueue.begin();
       iter != d_commandQueue.end(); ++iter) {
    Command* command = *iter;
    delete command;
  }
  d_commandQueue.clear();
  delete d_input;
}

Expr Parser::getSymbol(const std::string& name, SymbolType type) {
  checkDeclaration(name, CHECK_DECLARED, type);
  assert(isDeclared(name, type));

  if (type == SYM_VARIABLE) {
    // Functions share var namespace
    return d_symtab->lookup(name);
  }

  assert(false);  // Unhandled(type);
  return Expr();
}

Expr Parser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Expr Parser::getFunction(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

Type Parser::getType(const std::string& var_name, SymbolType type) {
  checkDeclaration(var_name, CHECK_DECLARED, type);
  assert(isDeclared(var_name, type));
  Type t = getSymbol(var_name, type).getType();
  return t;
}

Type Parser::getSort(const std::string& name) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  Type t = d_symtab->lookupType(name);
  return t;
}

Type Parser::getSort(const std::string& name, const std::vector<Type>& params) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  Type t = d_symtab->lookupType(name, params);
  return t;
}

size_t Parser::getArity(const std::string& sort_name) {
  checkDeclaration(sort_name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(sort_name, SYM_SORT));
  return d_symtab->lookupArity(sort_name);
}

/* Returns true if name is bound to a boolean variable. */
bool Parser::isBoolean(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isBoolean();
}

/* Returns true if name is bound to a function-like thing (function,
 * constructor, tester, or selector). */
bool Parser::isFunctionLike(const std::string& name) {
  if (!isDeclared(name, SYM_VARIABLE)) {
    return false;
  }
  Type type = getType(name);
  return type.isFunction() || type.isConstructor() || type.isTester() ||
         type.isSelector();
}

/* Returns true if name is bound to a defined function. */
bool Parser::isDefinedFunction(const std::string& name) {
  // more permissive in type than isFunction(), because defined
  // functions can be zero-ary and declared functions cannot.
  return d_symtab->isBoundDefinedFunction(name);
}

/* Returns true if the Expr is a defined function. */
bool Parser::isDefinedFunction(Expr func) {
  // more permissive in type than isFunction(), because defined
  // functions can be zero-ary and declared functions cannot.
  return d_symtab->isBoundDefinedFunction(func);
}

/* Returns true if name is bound to a function returning boolean. */
bool Parser::isPredicate(const std::string& name) {
  return isDeclared(name, SYM_VARIABLE) && getType(name).isPredicate();
}

Expr Parser::mkVar(const std::string& name, const Type& type, uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(name, type, flags);
  defineVar(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL);
  return expr;
}

Expr Parser::mkBoundVar(const std::string& name, const Type& type) {
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = d_exprManager->mkBoundVar(name, type);
  defineVar(name, expr, false);
  return expr;
}

Expr Parser::mkFunction(const std::string& name, const Type& type,
                        uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = d_exprManager->mkVar(name, type, flags);
  defineFunction(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL);
  return expr;
}

Expr Parser::mkAnonymousFunction(const std::string& prefix, const Type& type,
                                 uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  stringstream name;
  name << prefix << "_anon_" << ++d_anonymousFunctionCount;
  return d_exprManager->mkVar(name.str(), type, flags);
}

std::vector<Expr> Parser::mkVars(const std::vector<std::string> names,
                                 const Type& type, uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  std::vector<Expr> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type, flags));
  }
  return vars;
}

std::vector<Expr> Parser::mkBoundVars(const std::vector<std::string> names,
                                      const Type& type) {
  std::vector<Expr> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkBoundVar(names[i], type));
  }
  return vars;
}

void Parser::defineVar(const std::string& name, const Expr& val,
                       bool levelZero) {
  Debug("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  d_symtab->bind(name, val, levelZero);
  assert(isDeclared(name));
}

void Parser::defineFunction(const std::string& name, const Expr& val,
                            bool levelZero) {
  d_symtab->bindDefinedFunction(name, val, levelZero);
  assert(isDeclared(name));
}

void Parser::defineType(const std::string& name, const Type& type) {
  d_symtab->bindType(name, type);
  assert(isDeclared(name, SYM_SORT));
}

void Parser::defineType(const std::string& name,
                        const std::vector<Type>& params, const Type& type) {
  d_symtab->bindType(name, params, type);
  assert(isDeclared(name, SYM_SORT));
}

void Parser::defineParameterizedType(const std::string& name,
                                     const std::vector<Type>& params,
                                     const Type& type) {
  if (Debug.isOn("parser")) {
    Debug("parser") << "defineParameterizedType(" << name << ", "
                    << params.size() << ", [";
    if (params.size() > 0) {
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Type>(Debug("parser"), ", "));
      Debug("parser") << params.back();
    }
    Debug("parser") << "], " << type << ")" << std::endl;
  }
  defineType(name, params, type);
}

SortType Parser::mkSort(const std::string& name, uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  Type type = d_exprManager->mkSort(name, flags);
  defineType(name, type);
  return type;
}

SortConstructorType Parser::mkSortConstructor(const std::string& name,
                                              size_t arity) {
  Debug("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  SortConstructorType type = d_exprManager->mkSortConstructor(name, arity);
  defineType(name, vector<Type>(arity), type);
  return type;
}

SortType Parser::mkUnresolvedType(const std::string& name) {
  SortType unresolved = mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

SortConstructorType Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                                        size_t arity) {
  SortConstructorType unresolved = mkSortConstructor(name, arity);
  d_unresolved.insert(unresolved);
  return unresolved;
}

SortConstructorType Parser::mkUnresolvedTypeConstructor(
    const std::string& name, const std::vector<Type>& params) {
  Debug("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  SortConstructorType unresolved =
      d_exprManager->mkSortConstructor(name, params.size());
  defineType(name, params, unresolved);
  Type t = getSort(name, params);
  d_unresolved.insert(unresolved);
  return unresolved;
}

bool Parser::isUnresolvedType(const std::string& name) {
  if (!isDeclared(name, SYM_SORT)) {
    return false;
  }
  return d_unresolved.find(getSort(name)) != d_unresolved.end();
}

std::vector<DatatypeType> Parser::mkMutualDatatypeTypes(
    std::vector<Datatype>& datatypes) {
  try {
    std::vector<DatatypeType> types =
        d_exprManager->mkMutualDatatypeTypes(datatypes, d_unresolved);

    assert(datatypes.size() == types.size());

    for (unsigned i = 0; i < datatypes.size(); ++i) {
      DatatypeType t = types[i];
      const Datatype& dt = t.getDatatype();
      const std::string& name = dt.getName();
      Debug("parser-idt") << "define " << name << " as " << t << std::endl;
      if (isDeclared(name, SYM_SORT)) {
        throw ParserException(name + " already declared");
      }
      if (t.isParametric()) {
        std::vector<Type> paramTypes = t.getParamTypes();
        defineType(name, paramTypes, t);
      } else {
        defineType(name, t);
      }
      for (Datatype::const_iterator j = dt.begin(), j_end = dt.end();
           j != j_end; ++j) {
        const DatatypeConstructor& ctor = *j;
        expr::ExprPrintTypes::Scope pts(Debug("parser-idt"), true);
        Expr constructor = ctor.getConstructor();
        Debug("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if (isDeclared(constructorName, SYM_VARIABLE)) {
          throw ParserException(constructorName + " already declared");
        }
        defineVar(constructorName, constructor);
        Expr tester = ctor.getTester();
        Debug("parser-idt") << "+ define " << tester << std::endl;
        string testerName = ctor.getTesterName();
        if (isDeclared(testerName, SYM_VARIABLE)) {
          throw ParserException(testerName + " already declared");
        }
        defineVar(testerName, tester);
        for (DatatypeConstructor::const_iterator k = ctor.begin(),
                                                 k_end = ctor.end();
             k != k_end; ++k) {
          Expr selector = (*k).getSelector();
          Debug("parser-idt") << "+++ define " << selector << std::endl;
          string selectorName = (*k).getName();
          if (isDeclared(selectorName, SYM_VARIABLE)) {
            throw ParserException(selectorName + " already declared");
          }
          defineVar(selectorName, selector);
        }
      }
    }

    // These are no longer used, and the ExprManager would have
    // complained of a bad substitution if anything is left unresolved.
    // Clear out the set.
    d_unresolved.clear();

    // throw exception if any datatype is not well-founded
    for (unsigned i = 0; i < datatypes.size(); ++i) {
      const Datatype& dt = types[i].getDatatype();
      if (!dt.isCodatatype() && !dt.isWellFounded()) {
        throw ParserException(dt.getName() + " is not well-founded");
      }
    }

    return types;
  } catch (IllegalArgumentException& ie) {
    throw ParserException(ie.getMessage());
  }
}

bool Parser::isDeclared(const std::string& name, SymbolType type) {
  switch (type) {
    case SYM_VARIABLE:
      return d_reservedSymbols.find(name) != d_reservedSymbols.end() ||
             d_symtab->isBound(name);
    case SYM_SORT:
      return d_symtab->isBoundType(name);
  }
  assert(false);  // Unhandled(type);
  return false;
}

void Parser::reserveSymbolAtAssertionLevel(const std::string& varName) {
  checkDeclaration(varName, CHECK_UNDECLARED, SYM_VARIABLE);
  d_reservedSymbols.insert(varName);
}

void Parser::checkDeclaration(const std::string& varName,
                              DeclarationCheck check, SymbolType type,
                              std::string notes) throw(ParserException) {
  if (!d_checksEnabled) {
    return;
  }

  switch (check) {
    case CHECK_DECLARED:
      if (!isDeclared(varName, type)) {
        parseError("Symbol '" + varName + "' not declared as a " +
                   (type == SYM_VARIABLE ? "variable" : "type") +
                   (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_UNDECLARED:
      if (isDeclared(varName, type)) {
        parseError("Symbol '" + varName + "' previously declared as a " +
                   (type == SYM_VARIABLE ? "variable" : "type") +
                   (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_NONE:
      break;

    default:
      assert(false);  // Unhandled(check);
  }
}

void Parser::checkFunctionLike(const std::string& name) throw(ParserException) {
  if (d_checksEnabled && !isFunctionLike(name)) {
    parseError("Expecting function-like symbol, found '" + name + "'");
  }
}

void Parser::checkArity(Kind kind, unsigned numArgs) throw(ParserException) {
  if (!d_checksEnabled) {
    return;
  }

  unsigned min = d_exprManager->minArity(kind);
  unsigned max = d_exprManager->maxArity(kind);

  if (numArgs < min || numArgs > max) {
    stringstream ss;
    ss << "Expecting ";
    if (numArgs < min) {
      ss << "at least " << min << " ";
    } else {
      ss << "at most " << max << " ";
    }
    ss << "arguments for operator '" << kind << "', ";
    ss << "found " << numArgs;
    parseError(ss.str());
  }
}

void Parser::checkOperator(Kind kind, unsigned numArgs) throw(ParserException) {
  if (d_strictMode && d_logicOperators.find(kind) == d_logicOperators.end()) {
    parseError("Operator is not defined in the current logic: " +
               kindToString(kind));
  }
  checkArity(kind, numArgs);
}

void Parser::addOperator(Kind kind) { d_logicOperators.insert(kind); }

void Parser::preemptCommand(Command* cmd) { d_commandQueue.push_back(cmd); }

Command* Parser::nextCommand() throw(ParserException,
                                     UnsafeInterruptException) {
  Debug("parser") << "nextCommand()" << std::endl;
  Command* cmd = NULL;
  if (!d_commandQueue.empty()) {
    cmd = d_commandQueue.front();
    d_commandQueue.pop_front();
    setDone(cmd == NULL);
  } else {
    try {
      cmd = d_input->parseCommand();
      d_commandQueue.push_back(cmd);
      cmd = d_commandQueue.front();
      d_commandQueue.pop_front();
      setDone(cmd == NULL);
    } catch (ParserException& e) {
      setDone();
      throw;
    } catch (exception& e) {
      setDone();
      parseError(e.what());
    }
  }
  Debug("parser") << "nextCommand() => " << cmd << std::endl;
  if (cmd != NULL && dynamic_cast<SetOptionCommand*>(cmd) == NULL &&
      dynamic_cast<QuitCommand*>(cmd) == NULL) {
    // don't count set-option commands as to not get stuck in an infinite
    // loop of resourcing out
    const Options& options = d_exprManager->getOptions();
    d_resourceManager->spendResource(options.getParseStep());
  }
  return cmd;
}

Expr Parser::nextExpression() throw(ParserException, UnsafeInterruptException) {
  Debug("parser") << "nextExpression()" << std::endl;
  const Options& options = d_exprManager->getOptions();
  d_resourceManager->spendResource(options.getParseStep());
  Expr result;
  if (!done()) {
    try {
      result = d_input->parseExpr();
      setDone(result.isNull());
    } catch (ParserException& e) {
      setDone();
      throw;
    } catch (exception& e) {
      setDone();
      parseError(e.what());
    }
  }
  Debug("parser") << "nextExpression() => " << result << std::endl;
  return result;
}

void Parser::attributeNotSupported(const std::string& attr) {
  if (d_attributesWarnedAbout.find(attr) == d_attributesWarnedAbout.end()) {
    stringstream ss;
    ss << "warning: Attribute '" << attr
       << "' not supported (ignoring this and all following uses)";
    d_input->warning(ss.str());
    d_attributesWarnedAbout.insert(attr);
  }
}

} /* CVC4::parser namespace */
} /* CVC4 namespace */

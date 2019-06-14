/*********************                                                        */
/*! \file parser.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
#include <unordered_set>

#include "api/cvc4cpp.h"
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

Parser::Parser(api::Solver* solver,
               Input* input,
               bool strictMode,
               bool parseOnly)
    : d_resourceManager(solver->getExprManager()->getResourceManager()),
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
      d_forcedLogic(),
      d_solver(solver)
{
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

ExprManager* Parser::getExprManager() const
{
  return d_solver->getExprManager();
}

api::Solver* Parser::getSolver() const { return d_solver; }

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

Expr Parser::getExpressionForName(const std::string& name) {
  Type t;
  return getExpressionForNameAndType(name, t);
}

Expr Parser::getExpressionForNameAndType(const std::string& name, Type t) {
  assert( isDeclared(name) );
  // first check if the variable is declared and not overloaded
  Expr expr = getVariable(name);
  if(expr.isNull()) {
    // the variable is overloaded, try with type if the type exists
    if(!t.isNull()) {
      // if we decide later to support annotations for function types, this will update to 
      // separate t into ( argument types, return type )
      expr = getOverloadedConstantForType(name, t);
      if(expr.isNull()) {
        parseError("Cannot get overloaded constant for type ascription.");
      }
    }else{
      parseError("Overloaded constants must be type cast.");
    }
  }
  // now, post-process the expression
  assert( !expr.isNull() );
  Type te = expr.getType();
  if (te.isConstructor() && ConstructorType(te).getArity() == 0)
  {
    // nullary constructors have APPLY_CONSTRUCTOR kind with no children
    expr = getExprManager()->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, expr);
  }
  return expr;
}

Kind Parser::getKindForFunction(Expr fun) {
  if(isDefinedFunction(fun)) {
    return APPLY_UF;
  }
  Type t = fun.getType();
  if(t.isConstructor()) {
    return APPLY_CONSTRUCTOR;
  } else if(t.isSelector()) {
    return APPLY_SELECTOR;
  } else if(t.isTester()) {
    return APPLY_TESTER;
  } else if(t.isFunction()) {
    return APPLY_UF;
  }else{
    parseError("internal error: unhandled function application kind");
    return UNDEFINED_KIND;
  }
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
  Expr expr = getVariable(name);
  return !expr.isNull() && expr.getType().isBoolean();
}

bool Parser::isFunctionLike(Expr fun) {
  if(fun.isNull()) {
    return false;
  }
  Type type = fun.getType();
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
  Expr expr = getVariable(name);
  return !expr.isNull() && expr.getType().isPredicate();
}

Expr Parser::mkVar(const std::string& name, const Type& type, uint32_t flags, bool doOverload) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = getExprManager()->mkVar(name, type, flags);
  defineVar(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL, doOverload);
  return expr;
}

Expr Parser::mkBoundVar(const std::string& name, const Type& type) {
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = getExprManager()->mkBoundVar(name, type);
  defineVar(name, expr, false);
  return expr;
}

Expr Parser::mkFunction(const std::string& name, const Type& type,
                        uint32_t flags, bool doOverload) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  Expr expr = getExprManager()->mkVar(name, type, flags);
  defineFunction(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL, doOverload);
  return expr;
}

Expr Parser::mkAnonymousFunction(const std::string& prefix, const Type& type,
                                 uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  stringstream name;
  name << prefix << "_anon_" << ++d_anonymousFunctionCount;
  return getExprManager()->mkVar(name.str(), type, flags);
}

std::vector<Expr> Parser::mkVars(const std::vector<std::string> names,
                                 const Type& type, uint32_t flags, bool doOverload) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  std::vector<Expr> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type, flags, doOverload));
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
                       bool levelZero, bool doOverload) {
  Debug("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  if (!d_symtab->bind(name, val, levelZero, doOverload)) {
    std::stringstream ss;
    ss << "Cannot bind " << name << " to symbol of type " << val.getType();
    ss << ", maybe the symbol has already been defined?";
    parseError(ss.str()); 
  }
  assert(isDeclared(name));
}

void Parser::defineFunction(const std::string& name, const Expr& val,
                            bool levelZero, bool doOverload) {
  if (!d_symtab->bindDefinedFunction(name, val, levelZero, doOverload)) {
    std::stringstream ss;
    ss << "Failed to bind defined function " << name << " to symbol of type " << val.getType();
    parseError(ss.str()); 
  }
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
  Type type = getExprManager()->mkSort(name, flags);
  defineType(name, type);
  return type;
}

SortConstructorType Parser::mkSortConstructor(const std::string& name,
                                              size_t arity,
                                              uint32_t flags)
{
  Debug("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  SortConstructorType type =
      getExprManager()->mkSortConstructor(name, arity, flags);
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
  SortConstructorType unresolved =
      mkSortConstructor(name, arity, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

SortConstructorType Parser::mkUnresolvedTypeConstructor(
    const std::string& name, const std::vector<Type>& params) {
  Debug("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  SortConstructorType unresolved = getExprManager()->mkSortConstructor(
      name, params.size(), ExprManager::SORT_FLAG_PLACEHOLDER);
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
    std::vector<Datatype>& datatypes, bool doOverload) {
  try {
    std::vector<DatatypeType> types =
        getExprManager()->mkMutualDatatypeTypes(datatypes, d_unresolved);

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
      std::unordered_set< std::string > consNames;
      std::unordered_set< std::string > selNames;
      for (Datatype::const_iterator j = dt.begin(), j_end = dt.end();
           j != j_end; ++j) {
        const DatatypeConstructor& ctor = *j;
        expr::ExprPrintTypes::Scope pts(Debug("parser-idt"), true);
        Expr constructor = ctor.getConstructor();
        Debug("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if(consNames.find(constructorName)==consNames.end()) {
          if(!doOverload) {
            checkDeclaration(constructorName, CHECK_UNDECLARED);
          }
          defineVar(constructorName, constructor, false, doOverload);
          consNames.insert(constructorName);
        }else{
          throw ParserException(constructorName + " already declared in this datatype");
        }
        Expr tester = ctor.getTester();
        Debug("parser-idt") << "+ define " << tester << std::endl;
        string testerName = ctor.getTesterName();
        if(!doOverload) {
          checkDeclaration(testerName, CHECK_UNDECLARED);
        }
        defineVar(testerName, tester, false, doOverload);
        for (DatatypeConstructor::const_iterator k = ctor.begin(),
                                                 k_end = ctor.end();
             k != k_end; ++k) {
          Expr selector = (*k).getSelector();
          Debug("parser-idt") << "+++ define " << selector << std::endl;
          string selectorName = (*k).getName();
          if(selNames.find(selectorName)==selNames.end()) {
            if(!doOverload) {
              checkDeclaration(selectorName, CHECK_UNDECLARED);
            }
            defineVar(selectorName, selector, false, doOverload);
            selNames.insert(selectorName);
          }else{
            throw ParserException(selectorName + " already declared in this datatype");
          }
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

Type Parser::mkFlatFunctionType(std::vector<Type>& sorts,
                                Type range,
                                std::vector<Expr>& flattenVars)
{
  if (range.isFunction())
  {
    std::vector<Type> domainTypes =
        (static_cast<FunctionType>(range)).getArgTypes();
    for (unsigned i = 0, size = domainTypes.size(); i < size; i++)
    {
      sorts.push_back(domainTypes[i]);
      // the introduced variable is internal (not parsable)
      std::stringstream ss;
      ss << "__flatten_var_" << i;
      Expr v = getExprManager()->mkBoundVar(ss.str(), domainTypes[i]);
      flattenVars.push_back(v);
    }
    range = static_cast<FunctionType>(range).getRangeType();
  }
  if (sorts.empty())
  {
    return range;
  }
  return getExprManager()->mkFunctionType(sorts, range);
}

Type Parser::mkFlatFunctionType(std::vector<Type>& sorts, Type range)
{
  if (sorts.empty())
  {
    // no difference
    return range;
  }
  while (range.isFunction())
  {
    std::vector<Type> domainTypes =
        static_cast<FunctionType>(range).getArgTypes();
    sorts.insert(sorts.end(), domainTypes.begin(), domainTypes.end());
    range = static_cast<FunctionType>(range).getRangeType();
  }
  return getExprManager()->mkFunctionType(sorts, range);
}

Expr Parser::mkHoApply(Expr expr, std::vector<Expr>& args)
{
  for (unsigned i = 0; i < args.size(); i++)
  {
    expr = getExprManager()->mkExpr(HO_APPLY, expr, args[i]);
  }
  return expr;
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
                              DeclarationCheck check,
                              SymbolType type,
                              std::string notes)
{
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

void Parser::checkFunctionLike(Expr fun)
{
  if (d_checksEnabled && !isFunctionLike(fun)) {
    stringstream ss;
    ss << "Expecting function-like symbol, found '";
    ss << fun;
    ss << "'";
    parseError(ss.str());
  }
}

void Parser::checkArity(Kind kind, unsigned numArgs)
{
  if (!d_checksEnabled) {
    return;
  }

  unsigned min = getExprManager()->minArity(kind);
  unsigned max = getExprManager()->maxArity(kind);

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

void Parser::checkOperator(Kind kind, unsigned numArgs)
{
  if (d_strictMode && d_logicOperators.find(kind) == d_logicOperators.end()) {
    parseError("Operator is not defined in the current logic: " +
               kindToString(kind));
  }
  checkArity(kind, numArgs);
}

void Parser::addOperator(Kind kind) { d_logicOperators.insert(kind); }

void Parser::preemptCommand(Command* cmd) { d_commandQueue.push_back(cmd); }
Command* Parser::nextCommand()
{
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
    const Options& options = getExprManager()->getOptions();
    d_resourceManager->spendResource(options.getParseStep());
  }
  return cmd;
}

Expr Parser::nextExpression()
{
  Debug("parser") << "nextExpression()" << std::endl;
  const Options& options = getExprManager()->getOptions();
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

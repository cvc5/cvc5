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

api::Term Parser::getSymbol(const std::string& name, SymbolType type) {
  checkDeclaration(name, CHECK_DECLARED, type);
  assert(isDeclared(name, type));

  if (type == SYM_VARIABLE) {
    // Functions share var namespace
    return d_symtab->lookup(name);
  }

  assert(false);  // Unhandled(type);
  return Expr();
}

api::Term Parser::getVariable(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

api::Term Parser::getFunction(const std::string& name) {
  return getSymbol(name, SYM_VARIABLE);
}

api::Term Parser::getExpressionForName(const std::string& name) {
  api::Sort t;
  return getExpressionForNameAndType(name, t);
}

api::Term Parser::getExpressionForNameAndType(const std::string& name, api::Sort t) {
  assert(isDeclared(name));
  // first check if the variable is declared and not overloaded
  api::Term expr = getVariable(name);
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
  api::Sort te = expr.getSort();
  if (te.isConstructor() && te.getConstructorArity() == 0)
  {
    // nullary constructors have APPLY_CONSTRUCTOR kind with no children
    expr = api::Term(getExprManager()->mkExpr(CVC4::kind::APPLY_CONSTRUCTOR, expr.getExpr()));
  }
  return expr;
}

Kind Parser::getKindForFunction(api::Term fun) {
  api::Sort t = fun.getSort();
  if (t.isFunction())
  {
    return APPLY_UF;
  }
  else if (t.isConstructor())
  {
    return APPLY_CONSTRUCTOR;
  }
  else if (t.isSelector())
  {
    return APPLY_SELECTOR;
  }
  else if (t.isTester())
  {
    return APPLY_TESTER;
  }
  else
  {
    parseError("internal error: unhandled function application kind");
    return UNDEFINED_KIND;
  }
}

api::Sort Parser::getSort(const std::string& name) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  api::Sort t = api::Sort(d_symtab->lookupType(name));
  return t;
}

api::Sort Parser::getSort(const std::string& name, const std::vector<api::Sort>& params) {
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  api::Sort t = api::Sort(d_symtab->lookupType(name, api::convertSortVec(params)));
  return t;
}

size_t Parser::getArity(const std::string& sort_name) {
  checkDeclaration(sort_name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(sort_name, SYM_SORT));
  return d_symtab->lookupArity(sort_name);
}

/* Returns true if name is bound to a boolean variable. */
bool Parser::isBoolean(const std::string& name) {
  api::Term expr = getVariable(name);
  return !expr.isNull() && expr.getSort().isBoolean();
}

bool Parser::isFunctionLike(api::Term fun) {
  if(fun.isNull()) {
    return false;
  }
  api::Sort type = fun.getSort();
  return type.isFunction() || type.isConstructor() || type.isTester() ||
         type.isSelector();
}

/* Returns true if name is bound to a function returning boolean. */
bool Parser::isPredicate(const std::string& name) {
  api::Term expr = getVariable(name);
  return !expr.isNull() && expr.getSort().isPredicate();
}

api::Term Parser::mkVar(const std::string& name, const api::Sort& type, uint32_t flags, bool doOverload) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  api::Term expr = api::Term(getExprManager()->mkVar(name, type.getType(), flags));
  defineVar(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL, doOverload);
  return expr;
}

api::Term Parser::mkBoundVar(const std::string& name, const api::Sort& type) {
  Debug("parser") << "mkVar(" << name << ", " << type << ")" << std::endl;
  api::Term expr = api::Term(getExprManager()->mkBoundVar(name, type.getType()));
  defineVar(name, expr, false);
  return expr;
}

std::vector<api::Term> Parser::mkBoundVars(
    std::vector<std::pair<std::string, api::Sort> >& sortedVarNames)
{
  std::vector<api::Term> vars;
  for (std::pair<std::string, api::Sort>& i : sortedVarNames)
  {
    vars.push_back(mkBoundVar(i.first, i.second.getType()));
  }
  return vars;
}

api::Term Parser::mkAnonymousFunction(const std::string& prefix, const api::Sort& type,
                                 uint32_t flags) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  stringstream name;
  name << prefix << "_anon_" << ++d_anonymousFunctionCount;
  return api::Term(getExprManager()->mkVar(name.str(), type.getType(), flags));
}

std::vector<api::Term> Parser::mkVars(const std::vector<std::string> names,
                                 const api::Sort& type, uint32_t flags, bool doOverload) {
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  std::vector<api::Term> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkVar(names[i], type, flags, doOverload));
  }
  return vars;
}

std::vector<api::Term> Parser::mkBoundVars(const std::vector<std::string> names,
                                      const api::Sort& type) {
  std::vector<api::Term> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(mkBoundVar(names[i], type));
  }
  return vars;
}

void Parser::defineVar(const std::string& name, const api::Term& val,
                       bool levelZero, bool doOverload) {
  Debug("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  if (!d_symtab->bind(name, val.getExpr(), levelZero, doOverload)) {
    std::stringstream ss;
    ss << "Cannot bind " << name << " to symbol of type " << val.getSort();
    ss << ", maybe the symbol has already been defined?";
    parseError(ss.str()); 
  }
  assert(isDeclared(name));
}

void Parser::defineType(const std::string& name,
                        const api::Sort& type,
                        bool levelZero)
{
  d_symtab->bindType(name, type.getType(), levelZero);
  assert(isDeclared(name, SYM_SORT));
}

void Parser::defineType(const std::string& name,
                        const std::vector<api::Sort>& params,
                        const api::Sort& type,
                        bool levelZero)
{
  d_symtab->bindType(name, api::convertSortVec(params), type.getType(), levelZero);
  assert(isDeclared(name, SYM_SORT));
}

void Parser::defineParameterizedType(const std::string& name,
                                     const std::vector<api::Sort>& params,
                                     const api::Sort& type) {
  if (Debug.isOn("parser")) {
    Debug("parser") << "defineParameterizedType(" << name << ", "
                    << params.size() << ", [";
    if (params.size() > 0) {
      copy(params.begin(), params.end() - 1,
           ostream_iterator<api::Sort>(Debug("parser"), ", "));
      Debug("parser") << params.back();
    }
    Debug("parser") << "], " << type << ")" << std::endl;
  }
  defineType(name, params, type);
}

api::Sort Parser::mkSort(const std::string& name, uint32_t flags) {
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  api::Sort type = getExprManager()->mkSort(name, flags);
  defineType(
      name,
      type,
      d_globalDeclarations && !(flags & ExprManager::SORT_FLAG_PLACEHOLDER));
  return type;
}

api::Sort Parser::mkSortConstructor(const std::string& name,
                                              size_t arity,
                                              uint32_t flags)
{
  Debug("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  api::Sort type =
      getExprManager()->mkSortConstructor(name, arity, flags);
  defineType(
      name,
      vector<api::Sort>(arity),
      type,
      d_globalDeclarations && !(flags & ExprManager::SORT_FLAG_PLACEHOLDER));
  return type;
}

api::Sort Parser::mkUnresolvedType(const std::string& name) {
  api::Sort unresolved = mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                                        size_t arity) {
  api::Sort unresolved =
      mkSortConstructor(name, arity, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(
    const std::string& name, const std::vector<api::Sort>& params) {
  Debug("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  api::Sort unresolved = getExprManager()->mkSortConstructor(
      name, params.size(), ExprManager::SORT_FLAG_PLACEHOLDER);
  defineType(name, params, unresolved);
  api::Sort t = getSort(name, params);
  d_unresolved.insert(unresolved);
  return unresolved;
}

bool Parser::isUnresolvedType(const std::string& name) {
  if (!isDeclared(name, SYM_SORT)) {
    return false;
  }
  return d_unresolved.find(getSort(name)) != d_unresolved.end();
}

std::vector<api::Sort> Parser::mkMutualDatatypeTypes(
    std::vector<Datatype>& datatypes, bool doOverload) {
  try {
    std::set<CVC4::Type> tset = api::convertSortSet(d_unresolved);
    //std::vector<api::Sort> types =
    //    getExprManager()->mkMutualDatatypeTypes(datatypes, tset);
    std::vector<DatatypeType> dtypes =
        getExprManager()->mkMutualDatatypeTypes(datatypes, tset);
    std::vector<api::Sort> types;
    for (unsigned i=0, dtsize = dtypes.size(); i<dtsize; i++)
    {
      types.push_back(api::Sort(dtypes[i]));
    }

    assert(datatypes.size() == types.size());

    for (unsigned i = 0; i < datatypes.size(); ++i) {
      api::Sort t = types[i];
      const api::Datatype& dt = t.getDatatype();
      const std::string& name = dt.getName();
      Debug("parser-idt") << "define " << name << " as " << t << std::endl;
      if (isDeclared(name, SYM_SORT)) {
        throw ParserException(name + " already declared");
      }
      if (t.isParametricDatatype()) {
        std::vector<api::Sort> paramTypes = t.getDatatypeParamSorts();
        defineType(name, paramTypes, t, d_globalDeclarations);
      } else {
        defineType(name, t, d_globalDeclarations);
      }
      std::unordered_set< std::string > consNames;
      std::unordered_set< std::string > selNames;
      for (size_t j=0, ncons = dt.getNumConstructors(); j<ncons; j++)
      {
        const api::DatatypeConstructor& ctor = dt[j];
        expr::ExprPrintTypes::Scope pts(Debug("parser-idt"), true);
        api::Op constructor = ctor.getConstructorTerm();
        Debug("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if(consNames.find(constructorName)==consNames.end()) {
          if(!doOverload) {
            checkDeclaration(constructorName, CHECK_UNDECLARED);
          }
          defineVar(
              constructorName, constructor.getExpr(), d_globalDeclarations, doOverload);
          consNames.insert(constructorName);
        }else{
          throw ParserException(constructorName + " already declared in this datatype");
        }
        api::Op tester = ctor.getTesterTerm();
        Debug("parser-idt") << "+ define " << tester << std::endl;
        string testerName = ctor.getTesterName();
        if(!doOverload) {
          checkDeclaration(testerName, CHECK_UNDECLARED);
        }
        defineVar(testerName, tester.getExpr(), d_globalDeclarations, doOverload);
        for (size_t k=0, nargs = ctor.getNumArgs(); k<nargs; k++){
          const api::DatatypeSelector& sel = ctor[k];
          api::Op selector = sel.getSelectorTerm();
          Debug("parser-idt") << "+++ define " << selector << std::endl;
          string selectorName = sel.getName();
          if(selNames.find(selectorName)==selNames.end()) {
            if(!doOverload) {
              checkDeclaration(selectorName, CHECK_UNDECLARED);
            }
            defineVar(selectorName, selector.getExpr(), d_globalDeclarations, doOverload);
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
      const api::Datatype& dt = types[i].getDatatype();
      if (!dt.isCodatatype() && !dt.isWellFounded()) {
        throw ParserException(dt.getName() + " is not well-founded");
      }
    }

    return types;
  } catch (IllegalArgumentException& ie) {
    throw ParserException(ie.getMessage());
  }
}

api::Sort Parser::mkFlatFunctionType(std::vector<api::Sort>& sorts,
                                api::Sort range,
                                std::vector<api::Term>& flattenVars)
{
  if (range.isFunction())
  {
    std::vector<api::Sort> domainTypes = range.getFunctionDomainSorts();
    for (unsigned i = 0, size = domainTypes.size(); i < size; i++)
    {
      sorts.push_back(domainTypes[i]);
      // the introduced variable is internal (not parsable)
      std::stringstream ss;
      ss << "__flatten_var_" << i;
      api::Term v = api::Term(getExprManager()->mkBoundVar(ss.str(), domainTypes[i].getType()));
      flattenVars.push_back(v);
    }
    range = range.getFunctionCodomainSort();
  }
  if (sorts.empty())
  {
    return range;
  }
  return api::Sort(getExprManager()->mkFunctionType(api::convertSortVec(sorts), range.getType()));
}

api::Sort Parser::mkFlatFunctionType(std::vector<api::Sort>& sorts, api::Sort range)
{
  if (sorts.empty())
  {
    // no difference
    return range;
  }
  if (Debug.isOn("parser"))
  {
    Debug("parser") << "mkFlatFunctionType: range " << range << " and domains ";
    for (api::Sort t : sorts)
    {
      Debug("parser") << " " << t;
    }
    Debug("parser") << "\n";
  }
  while (range.isFunction())
  {
    std::vector<api::Sort> domainTypes = range.getFunctionDomainSorts();
    sorts.insert(sorts.end(), domainTypes.begin(), domainTypes.end());
    range = range.getFunctionCodomainSort();
  }
  return api::Sort(getExprManager()->mkFunctionType(api::convertSortVec(sorts), range.getType()));
}

api::Term Parser::mkHoApply(api::Term expr, std::vector<api::Term>& args)
{
  for (unsigned i = 0; i < args.size(); i++)
  {
    expr = api::Term(getExprManager()->mkExpr(HO_APPLY, expr.getExpr(), args[i].getExpr()));
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

void Parser::checkFunctionLike(api::Term fun)
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

void Parser::addOperator(api::Kind kind) { d_logicOperators.insert(kind); }

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

api::Term Parser::nextExpression()
{
  Debug("parser") << "nextExpression()" << std::endl;
  const Options& options = getExprManager()->getOptions();
  d_resourceManager->spendResource(options.getParseStep());
  api::Term result;
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

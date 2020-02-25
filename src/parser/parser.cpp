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

api::Term Parser::getSymbol(const std::string& name, SymbolType type)
{
  checkDeclaration(name, CHECK_DECLARED, type);
  assert(isDeclared(name, type));

  if (type == SYM_VARIABLE) {
    // Functions share var namespace
    return d_symtab->lookup(name);
  }

  assert(false);  // Unhandled(type);
  return Expr();
}

api::Term Parser::getVariable(const std::string& name)
{
  return getSymbol(name, SYM_VARIABLE);
}

api::Term Parser::getFunction(const std::string& name)
{
  return getSymbol(name, SYM_VARIABLE);
}

api::Term Parser::getExpressionForName(const std::string& name)
{
  api::Sort t;
  return getExpressionForNameAndType(name, t);
}

api::Term Parser::getExpressionForNameAndType(const std::string& name,
                                              api::Sort t)
{
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
    expr = d_solver->mkTerm(api::APPLY_CONSTRUCTOR, expr);
  }
  return expr;
}

api::Kind Parser::getKindForFunction(api::Term fun)
{
  api::Sort t = fun.getSort();
  if (t.isFunction())
  {
    return api::APPLY_UF;
  }
  else if (t.isConstructor())
  {
    return api::APPLY_CONSTRUCTOR;
  }
  else if (t.isSelector())
  {
    return api::APPLY_SELECTOR;
  }
  else if (t.isTester())
  {
    return api::APPLY_TESTER;
  }
  return api::UNDEFINED_KIND;
}

api::Sort Parser::getSort(const std::string& name)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  api::Sort t = api::Sort(d_symtab->lookupType(name));
  return t;
}

api::Sort Parser::getSort(const std::string& name,
                          const std::vector<api::Sort>& params)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  assert(isDeclared(name, SYM_SORT));
  api::Sort t =
      api::Sort(d_symtab->lookupType(name, api::sortVectorToTypes(params)));
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

bool Parser::isFunctionLike(api::Term fun)
{
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

api::Term Parser::bindVar(const std::string& name,
                          const api::Sort& type,
                          uint32_t flags,
                          bool doOverload)
{
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  Debug("parser") << "bindVar(" << name << ", " << type << ")" << std::endl;
  api::Term expr = mkVar(name, type, flags);
  defineVar(name, expr, flags & ExprManager::VAR_FLAG_GLOBAL, doOverload);
  return expr;
}

api::Term Parser::bindBoundVar(const std::string& name, const api::Sort& type)
{
  Debug("parser") << "bindBoundVar(" << name << ", " << type << ")"
                  << std::endl;
  api::Term expr = d_solver->mkVar(type, name);
  defineVar(name, expr, false);
  return expr;
}

std::vector<api::Term> Parser::bindBoundVars(
    std::vector<std::pair<std::string, api::Sort> >& sortedVarNames)
{
  std::vector<api::Term> vars;
  for (std::pair<std::string, api::Sort>& i : sortedVarNames)
  {
    vars.push_back(bindBoundVar(i.first, i.second.getType()));
  }
  return vars;
}

api::Term Parser::mkAnonymousFunction(const std::string& prefix,
                                      const api::Sort& type,
                                      uint32_t flags)
{
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  stringstream name;
  name << prefix << "_anon_" << ++d_anonymousFunctionCount;
  return mkVar(name.str(), type.getType(), flags);
}

std::vector<api::Term> Parser::bindVars(const std::vector<std::string> names,
                                        const api::Sort& type,
                                        uint32_t flags,
                                        bool doOverload)
{
  if (d_globalDeclarations) {
    flags |= ExprManager::VAR_FLAG_GLOBAL;
  }
  std::vector<api::Term> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(bindVar(names[i], type, flags, doOverload));
  }
  return vars;
}

std::vector<api::Term> Parser::bindBoundVars(
    const std::vector<std::string> names, const api::Sort& type)
{
  std::vector<api::Term> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(bindBoundVar(names[i], type));
  }
  return vars;
}

void Parser::defineVar(const std::string& name,
                       const api::Term& val,
                       bool levelZero,
                       bool doOverload)
{
  Debug("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  if (!d_symtab->bind(name, val.getExpr(), levelZero, doOverload))
  {
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
  d_symtab->bindType(
      name, api::sortVectorToTypes(params), type.getType(), levelZero);
  assert(isDeclared(name, SYM_SORT));
}

void Parser::defineParameterizedType(const std::string& name,
                                     const std::vector<api::Sort>& params,
                                     const api::Sort& type)
{
  if (Debug.isOn("parser")) {
    Debug("parser") << "defineParameterizedType(" << name << ", "
                    << params.size() << ", [";
    if (params.size() > 0) {
      copy(params.begin(),
           params.end() - 1,
           ostream_iterator<api::Sort>(Debug("parser"), ", "));
      Debug("parser") << params.back();
    }
    Debug("parser") << "], " << type << ")" << std::endl;
  }
  defineType(name, params, type);
}

api::Sort Parser::mkSort(const std::string& name, uint32_t flags)
{
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
  api::Sort type = getExprManager()->mkSortConstructor(name, arity, flags);
  defineType(
      name,
      vector<api::Sort>(arity),
      type,
      d_globalDeclarations && !(flags & ExprManager::SORT_FLAG_PLACEHOLDER));
  return type;
}

api::Sort Parser::mkUnresolvedType(const std::string& name)
{
  api::Sort unresolved = mkSort(name, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                              size_t arity)
{
  api::Sort unresolved =
      mkSortConstructor(name, arity, ExprManager::SORT_FLAG_PLACEHOLDER);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(
    const std::string& name, const std::vector<api::Sort>& params)
{
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

std::vector<DatatypeType> Parser::mkMutualDatatypeTypes(
    std::vector<Datatype>& datatypes, bool doOverload, uint32_t flags)
{
  try {
    std::set<Type> tset = api::sortSetToTypes(d_unresolved);
    std::vector<DatatypeType> dtypes =
        getExprManager()->mkMutualDatatypeTypes(datatypes, tset, flags);
    std::vector<api::Sort> types;
    for (unsigned i = 0, dtsize = dtypes.size(); i < dtsize; i++)
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
      if (t.isParametricDatatype())
      {
        std::vector<api::Sort> paramTypes = t.getDatatypeParamSorts();
        defineType(name, paramTypes, t, d_globalDeclarations);
      }
      else
      {
        defineType(name, t, d_globalDeclarations);
      }
      std::unordered_set< std::string > consNames;
      std::unordered_set< std::string > selNames;
      for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        const api::DatatypeConstructor& ctor = dt[j];
        expr::ExprPrintTypes::Scope pts(Debug("parser-idt"), true);
        api::Term constructor = ctor.getConstructorTerm();
        Debug("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if(consNames.find(constructorName)==consNames.end()) {
          if(!doOverload) {
            checkDeclaration(constructorName, CHECK_UNDECLARED);
          }
          defineVar(
              constructorName, constructor, d_globalDeclarations, doOverload);
          consNames.insert(constructorName);
        }else{
          throw ParserException(constructorName + " already declared in this datatype");
        }
        api::Term tester = ctor.getTesterTerm();
        Debug("parser-idt") << "+ define " << tester << std::endl;
        string testerName = ctor.getTesterName();
        if(!doOverload) {
          checkDeclaration(testerName, CHECK_UNDECLARED);
        }
        defineVar(testerName, tester, d_globalDeclarations, doOverload);
        for (size_t k = 0, nargs = ctor.getNumSelectors(); k < nargs; k++)
        {
          const api::DatatypeSelector& sel = ctor[k];
          api::Term selector = sel.getSelectorTerm();
          Debug("parser-idt") << "+++ define " << selector << std::endl;
          string selectorName = sel.getName();
          if(selNames.find(selectorName)==selNames.end()) {
            if(!doOverload) {
              checkDeclaration(selectorName, CHECK_UNDECLARED);
            }
            defineVar(selectorName, selector, d_globalDeclarations, doOverload);
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
    std::vector<DatatypeType> retTypes;
    for (unsigned i = 0, ntypes = types.size(); i < ntypes; i++)
    {
      retTypes.push_back(DatatypeType(types[i].getType()));
    }
    return retTypes;
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
      api::Term v = d_solver->mkVar(domainTypes[i], ss.str());
      flattenVars.push_back(v);
    }
    range = range.getFunctionCodomainSort();
  }
  if (sorts.empty())
  {
    return range;
  }
  return d_solver->mkFunctionSort(sorts, range);
}

api::Sort Parser::mkFlatFunctionType(std::vector<api::Sort>& sorts,
                                     api::Sort range)
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
  return d_solver->mkFunctionSort(sorts, range);
}

api::Term Parser::mkHoApply(api::Term expr, const std::vector<api::Term>& args)
{
  for (unsigned i = 0; i < args.size(); i++)
  {
    expr = d_solver->mkTerm(api::HO_APPLY, expr, args[i]);
  }
  return expr;
}

api::Term Parser::mkAssociative(api::Kind kind,
                                const std::vector<api::Term>& children)
{
  const size_t max = getExprManager()->maxArity(extToIntKind(kind));
  size_t numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if (numChildren <= max)
  {
    return d_solver->mkTerm(kind, children);
  }
  const size_t min = getExprManager()->minArity(extToIntKind(kind));

  std::vector<api::Term>::const_iterator it = children.begin();
  std::vector<api::Term>::const_iterator end = children.end();

  /* The new top-level children and the children of each sub node */
  std::vector<api::Term> newChildren;
  std::vector<api::Term> subChildren;

  while (it != end && numChildren > max)
  {
    /* Grab the next max children and make a node for them. */
    for (std::vector<api::Term>::const_iterator next = it + max; it != next;
         ++it, --numChildren)
    {
      subChildren.push_back(*it);
    }
    api::Term subTerm = d_solver->mkTerm(kind, subChildren);
    newChildren.push_back(subTerm);

    subChildren.clear();
  }

  // add the leftover children
  if (numChildren > 0)
  {
    for (; it != end; ++it)
    {
      newChildren.push_back(*it);
    }
  }

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  if (newChildren.size() >= min)
  {
    parseError("internal error: bad number of newChildren for mkAssociative");
  }

  // recurse
  return mkAssociative(kind, newChildren);
}

api::Term Parser::mkLeftAssociative(api::Kind kind,
                                    const std::vector<api::Term>& children)
{
  api::Term n = children[0];
  for (size_t i = 1, size = children.size(); i < size; i++)
  {
    n = d_solver->mkTerm(kind, n, children[i]);
  }
  return n;
}

api::Term Parser::mkRightAssociative(api::Kind kind,
                                     const std::vector<api::Term>& children)
{
  api::Term n = children[children.size() - 1];
  for (size_t i = children.size() - 1; i > 0;)
  {
    n = d_solver->mkTerm(kind, children[--i], n);
  }
  return n;
}

api::Term Parser::mkChain(api::Kind k, const std::vector<api::Term>& args)
{
  if (args.size() == 2)
  {
    // if this is the case exactly 1 pair will be generated so the
    // AND is not required
    return d_solver->mkTerm(k, args[0], args[1]);
  }
  std::vector<api::Term> children;
  for (size_t i = 0, nargsmo = args.size() - 1; i < nargsmo; i++)
  {
    children.push_back(d_solver->mkTerm(k, args[i], args[i + 1]));
  }
  return d_solver->mkTerm(api::AND, children);
}

//!!!!!!!!!!! temporary
api::Term Parser::mkBuiltinApp(api::Term f,
                               const std::vector<api::Term>& args) const
{
  return api::Term(
      getExprManager()->mkExpr(f.getExpr(), termVectorToExprs(args)));
}

api::Term Parser::mkBuiltinApp(api::Term f, api::Term t1) const
{
  std::vector<api::Term> args;
  args.push_back(t1);
  return mkBuiltinApp(f, args);
}
api::Term Parser::mkBuiltinApp(api::Term f, api::Term t1, api::Term t2) const
{
  std::vector<api::Term> args;
  args.push_back(t1);
  args.push_back(t2);
  return mkBuiltinApp(f, args);
}

api::Term Parser::applyTypeAscription(api::Term t, api::Sort s)
{
  api::Kind k = t.getKind();
  // These are not casts, they are due to the fact that our syntax for them
  // involves a type ascription. In actuality, these should be
  // understood as symbols indexed by types. However, SMT-LIB does not
  // permit types as indices, so we must use, e.g. (as emptyset (Set T))
  // instead of (_ emptyset (Set T)).
  if (k == api::EMPTYSET)
  {
    return d_solver->mkEmptySet(s);
  }
  else if (k == api::UNIVERSE_SET)
  {
    return d_solver->mkUniverseSet(s);
  }
  else if (k == api::SEP_NIL)
  {
    return d_solver->mkSepNil(s);
  }
  else if (k == api::APPLY_CONSTRUCTOR)
  {
    std::vector<api::Term> children;
    children.insert(children.end(),t.begin(),t.end());
    children[0] = castConstructor(children[0], s);
    t = d_solver->mkTerm(api::APPLY_CONSTRUCTOR,children);
    return t;
  }
  // otherwise, no cast
  return t;
}

api::Term Parser::castConstructor(api::Term t, api::Sort s)
{
  /*
  api::Sort etype = t.getSort();
  // get the datatype that t belongs to
  api::Sort etyped = etype.getConstructorCodomainSort();
  api::Datatype d = etyped.getDatatype();
  // lookup by name
  api::DatatypeConstructor dc = d.getConstructor(t.toString());
      
  // a non-nullary constructor with a type ascription
  if (s.isParametricDatatype())
  {
    ExprManager* em = getExprManager();
    // apply type ascription to the operator
    Expr e = t.getExpr();
    const DatatypeConstructor& dtc =
        Datatype::datatypeOf(e)[Datatype::indexOf(e)];
    t = api::Term(
        em->mkExpr(kind::APPLY_TYPE_ASCRIPTION,
                    em->mkConst(AscriptionType(
                        dtc.getSpecializedConstructorType(s.getType()))),
                    e));
  }
  */
  if(!t.getSort().isConstructor())
  {
    std::stringstream ss;
    ss << "expecting constructor in castConstructor, got " << t << std::endl;
    parseError(ss.str());
  }
  if(!s.isDatatype())
  {
    std::stringstream ss;
    ss << "expecting datatype in castConstructor, got " << s << std::endl;
    parseError(ss.str());
  }
  api::Sort etype = t.getSort();
  // get the datatype that t belongs to
  api::Sort etyped = etype.getConstructorCodomainSort();
  api::Datatype d = etyped.getDatatype();
  // lookup by name
  api::DatatypeConstructor dc = d.getConstructor(t.toString());
      
  // a non-nullary constructor with a type ascription
  if (s.isParametricDatatype())
  {
    ExprManager* em = getExprManager();
    // apply type ascription to the operator
    Expr e = t.getExpr();
    const DatatypeConstructor& dtc =
        Datatype::datatypeOf(e)[Datatype::indexOf(e)];
    t = api::Term(
        em->mkExpr(kind::APPLY_TYPE_ASCRIPTION,
                    em->mkConst(AscriptionType(
                        dtc.getSpecializedConstructorType(s.getType()))),
                    e));
  }
  return t;
}

api::Term Parser::mkVar(const std::string& name,
                        const api::Sort& type,
                        uint32_t flags)
{
  return api::Term(getExprManager()->mkVar(name, type.getType(), flags));
}

//!!!!!!!!!!! temporary

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

void Parser::checkArity(api::Kind kind, unsigned numArgs)
{
  if (!d_checksEnabled) {
    return;
  }

  unsigned min = getExprManager()->minArity(extToIntKind(kind));
  unsigned max = getExprManager()->maxArity(extToIntKind(kind));

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

void Parser::checkOperator(api::Kind kind, unsigned numArgs)
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
    d_resourceManager->spendResource(ResourceManager::Resource::ParseStep);
  }
  return cmd;
}

api::Term Parser::nextExpression()
{
  Debug("parser") << "nextExpression()" << std::endl;
  d_resourceManager->spendResource(ResourceManager::Resource::ParseStep);
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

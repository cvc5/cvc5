/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Christopher L. Conway
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Parser state implementation.
 */

#include "parser/parser.h"

#include <clocale>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <unordered_set>

#include "api/cpp/cvc5.h"
#include "base/check.h"
#include "base/output.h"
#include "expr/kind.h"
#include "options/options.h"
#include "parser/input.h"
#include "parser/parser_exception.h"
#include "smt/command.h"

using namespace std;
using namespace cvc5::kind;

namespace cvc5 {
namespace parser {

Parser::Parser(api::Solver* solver,
               SymbolManager* sm,
               bool strictMode,
               bool parseOnly)
    : d_symman(sm),
      d_symtab(sm->getSymbolTable()),
      d_assertionLevel(0),
      d_anonymousFunctionCount(0),
      d_done(true),
      d_checksEnabled(true),
      d_strictMode(strictMode),
      d_parseOnly(parseOnly),
      d_canIncludeFile(true),
      d_logicIsForced(false),
      d_forcedLogic(),
      d_solver(solver)
{
}

Parser::~Parser() {
  for (std::list<Command*>::iterator iter = d_commandQueue.begin();
       iter != d_commandQueue.end(); ++iter) {
    Command* command = *iter;
    delete command;
  }
  d_commandQueue.clear();
}

api::Solver* Parser::getSolver() const { return d_solver; }

api::Term Parser::getSymbol(const std::string& name, SymbolType type)
{
  checkDeclaration(name, CHECK_DECLARED, type);
  Assert(isDeclared(name, type));
  Assert(type == SYM_VARIABLE);
  // Functions share var namespace
  return d_symtab->lookup(name);
}

void Parser::forceLogic(const std::string& logic)
{
  Assert(!d_logicIsForced);
  d_logicIsForced = true;
  d_forcedLogic = logic;
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
  Assert(isDeclared(name));
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
  Assert(!expr.isNull());
  api::Sort te = expr.getSort();
  if (te.isConstructor() && te.getConstructorArity() == 0)
  {
    // nullary constructors have APPLY_CONSTRUCTOR kind with no children
    expr = d_solver->mkTerm(api::APPLY_CONSTRUCTOR, expr);
  }
  return expr;
}

bool Parser::getTesterName(api::Term cons, std::string& name) { return false; }

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
  else if (t.isUpdater())
  {
    return api::APPLY_UPDATER;
  }
  return api::UNDEFINED_KIND;
}

api::Sort Parser::getSort(const std::string& name)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert(isDeclared(name, SYM_SORT));
  api::Sort t = d_symtab->lookupType(name);
  return t;
}

api::Sort Parser::getSort(const std::string& name,
                          const std::vector<api::Sort>& params)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert(isDeclared(name, SYM_SORT));
  api::Sort t = d_symtab->lookupType(name, params);
  return t;
}

size_t Parser::getArity(const std::string& sort_name) {
  checkDeclaration(sort_name, CHECK_DECLARED, SYM_SORT);
  Assert(isDeclared(sort_name, SYM_SORT));
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
                          bool levelZero,
                          bool doOverload)
{
  bool globalDecls = d_symman->getGlobalDeclarations();
  Debug("parser") << "bindVar(" << name << ", " << type << ")" << std::endl;
  api::Term expr = d_solver->mkConst(type, name);
  defineVar(name, expr, globalDecls || levelZero, doOverload);
  return expr;
}

api::Term Parser::bindBoundVar(const std::string& name, const api::Sort& type)
{
  Debug("parser") << "bindBoundVar(" << name << ", " << type << ")"
                  << std::endl;
  api::Term expr = d_solver->mkVar(type, name);
  defineVar(name, expr);
  return expr;
}

std::vector<api::Term> Parser::bindBoundVars(
    std::vector<std::pair<std::string, api::Sort> >& sortedVarNames)
{
  std::vector<api::Term> vars;
  for (std::pair<std::string, api::Sort>& i : sortedVarNames)
  {
    vars.push_back(bindBoundVar(i.first, i.second));
  }
  return vars;
}

std::vector<api::Term> Parser::bindVars(const std::vector<std::string> names,
                                        const api::Sort& type,
                                        bool levelZero,
                                        bool doOverload)
{
  std::vector<api::Term> vars;
  for (unsigned i = 0; i < names.size(); ++i) {
    vars.push_back(bindVar(names[i], type, levelZero, doOverload));
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
  if (!d_symtab->bind(name, val, levelZero, doOverload))
  {
    std::stringstream ss;
    ss << "Cannot bind " << name << " to symbol of type " << val.getSort();
    ss << ", maybe the symbol has already been defined?";
    parseError(ss.str());
  }
  Assert(isDeclared(name));
}

void Parser::defineType(const std::string& name,
                        const api::Sort& type,
                        bool levelZero,
                        bool skipExisting)
{
  if (skipExisting && isDeclared(name, SYM_SORT))
  {
    Assert(d_symtab->lookupType(name) == type);
    return;
  }
  d_symtab->bindType(name, type, levelZero);
  Assert(isDeclared(name, SYM_SORT));
}

void Parser::defineType(const std::string& name,
                        const std::vector<api::Sort>& params,
                        const api::Sort& type,
                        bool levelZero)
{
  d_symtab->bindType(name, params, type, levelZero);
  Assert(isDeclared(name, SYM_SORT));
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

api::Sort Parser::mkSort(const std::string& name)
{
  Debug("parser") << "newSort(" << name << ")" << std::endl;
  bool globalDecls = d_symman->getGlobalDeclarations();
  api::Sort type = d_solver->mkUninterpretedSort(name);
  defineType(name, type, globalDecls);
  return type;
}

api::Sort Parser::mkSortConstructor(const std::string& name, size_t arity)
{
  Debug("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  bool globalDecls = d_symman->getGlobalDeclarations();
  api::Sort type = d_solver->mkSortConstructorSort(name, arity);
  defineType(name, vector<api::Sort>(arity), type, globalDecls);
  return type;
}

api::Sort Parser::mkUnresolvedType(const std::string& name)
{
  api::Sort unresolved = d_solver->mkUninterpretedSort(name);
  defineType(name, unresolved);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(const std::string& name,
                                              size_t arity)
{
  api::Sort unresolved = d_solver->mkSortConstructorSort(name, arity);
  defineType(name, vector<api::Sort>(arity), unresolved);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedTypeConstructor(
    const std::string& name, const std::vector<api::Sort>& params)
{
  Debug("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  api::Sort unresolved = d_solver->mkSortConstructorSort(name, params.size());
  defineType(name, params, unresolved);
  api::Sort t = getSort(name, params);
  d_unresolved.insert(unresolved);
  return unresolved;
}

api::Sort Parser::mkUnresolvedType(const std::string& name, size_t arity)
{
  if (arity == 0)
  {
    return mkUnresolvedType(name);
  }
  return mkUnresolvedTypeConstructor(name, arity);
}

bool Parser::isUnresolvedType(const std::string& name) {
  if (!isDeclared(name, SYM_SORT)) {
    return false;
  }
  return d_unresolved.find(getSort(name)) != d_unresolved.end();
}

std::vector<api::Sort> Parser::bindMutualDatatypeTypes(
    std::vector<api::DatatypeDecl>& datatypes, bool doOverload)
{
  try {
    std::vector<api::Sort> types =
        d_solver->mkDatatypeSorts(datatypes, d_unresolved);

    Assert(datatypes.size() == types.size());
    bool globalDecls = d_symman->getGlobalDeclarations();

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
        defineType(name, paramTypes, t, globalDecls);
      }
      else
      {
        defineType(name, t, globalDecls);
      }
      std::unordered_set< std::string > consNames;
      std::unordered_set< std::string > selNames;
      for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        const api::DatatypeConstructor& ctor = dt[j];
        api::Term constructor = ctor.getConstructorTerm();
        Debug("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if(consNames.find(constructorName)==consNames.end()) {
          if(!doOverload) {
            checkDeclaration(constructorName, CHECK_UNDECLARED);
          }
          defineVar(constructorName, constructor, globalDecls, doOverload);
          consNames.insert(constructorName);
        }else{
          throw ParserException(constructorName + " already declared in this datatype");
        }
        std::string testerName;
        if (getTesterName(constructor, testerName))
        {
          api::Term tester = ctor.getTesterTerm();
          Debug("parser-idt") << "+ define " << testerName << std::endl;
          if (!doOverload)
          {
            checkDeclaration(testerName, CHECK_UNDECLARED);
          }
          defineVar(testerName, tester, globalDecls, doOverload);
        }
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
            defineVar(selectorName, selector, globalDecls, doOverload);
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

api::Term Parser::applyTypeAscription(api::Term t, api::Sort s)
{
  api::Kind k = t.getKind();
  if (k == api::EMPTYSET)
  {
    t = d_solver->mkEmptySet(s);
  }
  else if (k == api::EMPTYBAG)
  {
    t = d_solver->mkEmptyBag(s);
  }
  else if (k == api::CONST_SEQUENCE)
  {
    if (!s.isSequence())
    {
      std::stringstream ss;
      ss << "Type ascription on empty sequence must be a sequence, got " << s;
      parseError(ss.str());
    }
    if (!t.getConstSequenceElements().empty())
    {
      std::stringstream ss;
      ss << "Cannot apply a type ascription to a non-empty sequence";
      parseError(ss.str());
    }
    t = d_solver->mkEmptySequence(s.getSequenceElementSort());
  }
  else if (k == api::UNIVERSE_SET)
  {
    t = d_solver->mkUniverseSet(s);
  }
  else if (k == api::SEP_NIL)
  {
    t = d_solver->mkSepNil(s);
  }
  else if (k == api::APPLY_CONSTRUCTOR)
  {
    std::vector<api::Term> children(t.begin(), t.end());
    // apply type ascription to the operator and reconstruct
    children[0] = applyTypeAscription(children[0], s);
    t = d_solver->mkTerm(api::APPLY_CONSTRUCTOR, children);
  }
  // !!! temporary until datatypes are refactored in the new API
  api::Sort etype = t.getSort();
  if (etype.isConstructor())
  {
    // Type ascriptions only have an effect on the node structure if this is a
    // parametric datatype.
    if (s.isParametricDatatype())
    {
      // get the datatype that t belongs to
      api::Sort etyped = etype.getConstructorCodomainSort();
      api::Datatype d = etyped.getDatatype();
      // lookup by name
      api::DatatypeConstructor dc = d.getConstructor(t.toString());
      // ask the constructor for the specialized constructor term
      t = dc.getSpecializedConstructorTerm(s);
    }
    // the type of t does not match the sort s by design (constructor type
    // vs datatype type), thus we use an alternative check here.
    if (t.getSort().getConstructorCodomainSort() != s)
    {
      std::stringstream ss;
      ss << "Type ascription on constructor not satisfied, term " << t
         << " expected sort " << s << " but has sort "
         << t.getSort().getConstructorCodomainSort();
      parseError(ss.str());
    }
    return t;
  }
  // otherwise, nothing to do
  // check that the type is correct
  if (t.getSort() != s)
  {
    std::stringstream ss;
    ss << "Type ascription not satisfied, term " << t << " expected sort " << s
       << " but has sort " << t.getSort();
    parseError(ss.str());
  }
  return t;
}

bool Parser::isDeclared(const std::string& name, SymbolType type) {
  switch (type) {
    case SYM_VARIABLE: return d_symtab->isBound(name);
    case SYM_SORT:
      return d_symtab->isBoundType(name);
  }
  Assert(false);  // Unhandled(type);
  return false;
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

    default: Assert(false);  // Unhandled(check);
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
  return cmd;
}

api::Term Parser::nextExpression()
{
  Debug("parser") << "nextExpression()" << std::endl;
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

size_t Parser::scopeLevel() const { return d_symman->scopeLevel(); }

void Parser::pushScope(bool isUserContext)
{
  d_symman->pushScope(isUserContext);
}

void Parser::popScope()
{
  d_symman->popScope();
}

void Parser::reset() {}

SymbolManager* Parser::getSymbolManager() { return d_symman; }

std::wstring Parser::processAdHocStringEsc(const std::string& s)
{
  std::wstring ws;
  {
    std::setlocale(LC_ALL, "en_US.utf8");
    std::mbtowc(nullptr, nullptr, 0);
    const char* end = s.data() + s.size();
    const char* ptr = s.data();
    for (wchar_t c; ptr != end; ) {
      int res = std::mbtowc(&c, ptr, end - ptr);
      if (res == -1) {
        std::cerr << "Invalid escape sequence in " << s << std::endl;
        break;
      } else if (res == 0) {
        break;
      } else {
        ws += c;
        ptr += res;
      }
    }
  }

  std::wstring res;
  unsigned i = 0;
  while (i < ws.size())
  {
    // get the current character
    if (ws[i] != '\\')
    {
      // don't worry about printable here
      res.push_back(ws[i]);
      ++i;
      continue;
    }
    // slash is always escaped
    ++i;
    if (i >= ws.size())
    {
      // slash cannot be the last character if we are parsing escape sequences
      std::stringstream serr;
      serr << "Escape sequence at the end of string: \"" << s
           << "\" should be handled by lexer";
      parseError(serr.str());
    }
    switch (ws[i])
    {
      case 'n':
      {
        res.push_back('\n');
        i++;
      }
      break;
      case 't':
      {
        res.push_back('\t');
        i++;
      }
      break;
      case 'v':
      {
        res.push_back('\v');
        i++;
      }
      break;
      case 'b':
      {
        res.push_back('\b');
        i++;
      }
      break;
      case 'r':
      {
        res.push_back('\r');
        i++;
      }
      break;
      case 'f':
      {
        res.push_back('\f');
        i++;
      }
      break;
      case 'a':
      {
        res.push_back('\a');
        i++;
      }
      break;
      case '\\':
      {
        res.push_back('\\');
        i++;
      }
      break;
      case 'x':
      {
        bool isValid = false;
        if (i + 2 < ws.size())
        {
          if (std::isxdigit(ws[i + 1]) && std::isxdigit(ws[i + 2]))
          {
            std::wstringstream shex;
            shex << ws[i + 1] << ws[i + 2];
            unsigned val;
            shex >> std::hex >> val;
            res.push_back(val);
            i += 3;
            isValid = true;
          }
        }
        if (!isValid)
        {
          std::stringstream serr;
          serr << "Illegal String Literal: \"" << s
               << "\", must have two digits after \\x";
          parseError(serr.str());
        }
      }
      break;
      default:
      {
        if (std::isdigit(ws[i]))
        {
          // octal escape sequences  TODO : revisit (issue #1251).
          unsigned num = static_cast<unsigned>(ws[i]) - 48;
          bool flag = num < 4;
          if (i + 1 < ws.size() && num < 8 && std::isdigit(ws[i + 1])
              && ws[i + 1] < '8')
          {
            num = num * 8 + static_cast<unsigned>(ws[i + 1]) - 48;
            if (flag && i + 2 < ws.size() && std::isdigit(ws[i + 2])
                && ws[i + 2] < '8')
            {
              num = num * 8 + static_cast<unsigned>(ws[i + 2]) - 48;
              res.push_back(num);
              i += 3;
            }
            else
            {
              res.push_back(num);
              i += 2;
            }
          }
          else
          {
            res.push_back(num);
            i++;
          }
        }
      }
    }
  }
  return res;
}

api::Term Parser::mkStringConstant(const std::string& s)
{
  if (language::isInputLang_smt2_6(d_solver->getOptions().getInputLanguage()))
  {
    return d_solver->mkString(s, true);
  }
  // otherwise, we must process ad-hoc escape sequences
  std::wstring str = processAdHocStringEsc(s);
  return d_solver->mkString(str);
}

api::Term Parser::mkCharConstant(const std::string& s)
{
  Assert(s.find_first_not_of("0123456789abcdefABCDEF", 0) == std::string::npos
         && s.size() <= 5 && s.size() > 0)
      << "Unexpected string for hexadecimal character " << s;
  wchar_t val = static_cast<wchar_t>(std::stoul(s, 0, 16));
  return d_solver->mkString(std::wstring(1, val));
}

}  // namespace parser
}  // namespace cvc5

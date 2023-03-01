/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
#include "parser/api/cpp/command.h"
#include "parser/input.h"
#include "parser/parser_exception.h"
#include "parser/smt2/smt2_input.h"

using namespace std;

namespace cvc5 {
namespace parser {

ParserState::ParserState(ParserStateCallback* psc,
                         Solver* solver,
                         SymbolManager* sm,
                         bool strictMode)
    : d_solver(solver),
      d_psc(psc),
      d_symman(sm),
      d_symtab(sm->getSymbolTable()),
      d_checksEnabled(true),
      d_strictMode(strictMode),
      d_parseOnly(d_solver->getOptionInfo("parse-only").boolValue())
{
}

ParserState::~ParserState() {}

Solver* ParserState::getSolver() const { return d_solver; }

Term ParserState::getSymbol(const std::string& name, SymbolType type)
{
  checkDeclaration(name, CHECK_DECLARED, type);
  Assert(isDeclared(name, type));
  Assert(type == SYM_VARIABLE);
  // Functions share var namespace
  return d_symtab->lookup(name);
}
std::string ParserState::getNameForUserName(const std::string& name) const
{
  if (!d_printNamespace.empty())
  {
    std::stringstream ss;
    ss << d_printNamespace << name;
    return ss.str();
  }
  return name;
}

const std::string& ParserState::getForcedLogic() const
{
  return d_symman->getForcedLogic();
}
bool ParserState::logicIsForced() const { return d_symman->isLogicForced(); }

Term ParserState::getVariable(const std::string& name)
{
  return getSymbol(name, SYM_VARIABLE);
}

Term ParserState::getFunction(const std::string& name)
{
  return getSymbol(name, SYM_VARIABLE);
}

Term ParserState::getExpressionForName(const std::string& name)
{
  Sort t;
  return getExpressionForNameAndType(name, t);
}

Term ParserState::getExpressionForNameAndType(const std::string& name, Sort t)
{
  Assert(isDeclared(name));
  // first check if the variable is declared and not overloaded
  Term expr = getVariable(name);
  if (expr.isNull())
  {
    // the variable is overloaded, try with type if the type exists
    if (!t.isNull())
    {
      // if we decide later to support annotations for function types, this will
      // update to separate t into ( argument types, return type )
      expr = getOverloadedConstantForType(name, t);
      if (expr.isNull())
      {
        parseError("Cannot get overloaded constant for type ascription.");
      }
    }
    else
    {
      parseError("Overloaded constants must be type cast.");
    }
  }
  // now, post-process the expression
  Assert(!expr.isNull());
  Sort te = expr.getSort();
  if (te.isDatatypeConstructor() && te.getDatatypeConstructorArity() == 0)
  {
    // nullary constructors have APPLY_CONSTRUCTOR kind with no children
    expr = d_solver->mkTerm(APPLY_CONSTRUCTOR, {expr});
  }
  return expr;
}

bool ParserState::getTesterName(Term cons, std::string& name) { return false; }

Kind ParserState::getKindForFunction(Term fun)
{
  Sort t = fun.getSort();
  if (t.isFunction())
  {
    return APPLY_UF;
  }
  else if (t.isDatatypeConstructor())
  {
    return APPLY_CONSTRUCTOR;
  }
  else if (t.isDatatypeSelector())
  {
    return APPLY_SELECTOR;
  }
  else if (t.isDatatypeTester())
  {
    return APPLY_TESTER;
  }
  else if (t.isDatatypeUpdater())
  {
    return APPLY_UPDATER;
  }
  return UNDEFINED_KIND;
}

Sort ParserState::getSort(const std::string& name)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert(isDeclared(name, SYM_SORT));
  Sort t = d_symtab->lookupType(name);
  return t;
}

Sort ParserState::getParametricSort(const std::string& name,
                                    const std::vector<Sort>& params)
{
  checkDeclaration(name, CHECK_DECLARED, SYM_SORT);
  Assert(isDeclared(name, SYM_SORT));
  Sort t = d_symtab->lookupType(name, params);
  return t;
}

bool ParserState::isFunctionLike(Term fun)
{
  if (fun.isNull())
  {
    return false;
  }
  Sort type = fun.getSort();
  return type.isFunction() || type.isDatatypeConstructor()
         || type.isDatatypeTester() || type.isDatatypeSelector();
}

Term ParserState::bindVar(const std::string& name,
                          const Sort& type,
                          bool doOverload)
{
  Trace("parser") << "bindVar(" << name << ", " << type << ")" << std::endl;
  Term expr = d_solver->mkConst(type, getNameForUserName(name));
  defineVar(name, expr, doOverload);
  return expr;
}

Term ParserState::bindBoundVar(const std::string& name, const Sort& type)
{
  Trace("parser") << "bindBoundVar(" << name << ", " << type << ")"
                  << std::endl;
  Term expr = d_solver->mkVar(type, name);
  defineVar(name, expr);
  return expr;
}

std::vector<Term> ParserState::bindBoundVars(
    std::vector<std::pair<std::string, Sort> >& sortedVarNames)
{
  std::vector<Term> vars;
  for (std::pair<std::string, Sort>& i : sortedVarNames)
  {
    vars.push_back(bindBoundVar(i.first, i.second));
  }
  return vars;
}

std::vector<Term> ParserState::bindBoundVars(
    const std::vector<std::string> names, const Sort& type)
{
  std::vector<Term> vars;
  for (unsigned i = 0; i < names.size(); ++i)
  {
    vars.push_back(bindBoundVar(names[i], type));
  }
  return vars;
}

void ParserState::defineVar(const std::string& name,
                            const Term& val,
                            bool doOverload)
{
  Trace("parser") << "defineVar( " << name << " := " << val << ")" << std::endl;
  if (!d_symtab->bind(name, val, doOverload))
  {
    std::stringstream ss;
    ss << "Cannot bind " << name << " to symbol of type " << val.getSort();
    ss << ", maybe the symbol has already been defined?";
    parseError(ss.str());
  }
  Assert(isDeclared(name));
}

void ParserState::defineType(const std::string& name,
                             const Sort& type,
                             bool skipExisting)
{
  if (skipExisting && isDeclared(name, SYM_SORT))
  {
    Assert(d_symtab->lookupType(name) == type);
    return;
  }
  d_symtab->bindType(name, type);
  Assert(isDeclared(name, SYM_SORT));
}

void ParserState::defineType(const std::string& name,
                             const std::vector<Sort>& params,
                             const Sort& type)
{
  d_symtab->bindType(name, params, type);
  Assert(isDeclared(name, SYM_SORT));
}

void ParserState::defineParameterizedType(const std::string& name,
                                          const std::vector<Sort>& params,
                                          const Sort& type)
{
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "defineParameterizedType(" << name << ", "
                    << params.size() << ", [";
    if (params.size() > 0)
    {
      copy(params.begin(),
           params.end() - 1,
           ostream_iterator<Sort>(Trace("parser"), ", "));
      Trace("parser") << params.back();
    }
    Trace("parser") << "], " << type << ")" << std::endl;
  }
  defineType(name, params, type);
}

Sort ParserState::mkSort(const std::string& name)
{
  Trace("parser") << "newSort(" << name << ")" << std::endl;
  Sort type = d_solver->mkUninterpretedSort(getNameForUserName(name));
  defineType(name, type);
  return type;
}

Sort ParserState::mkSortConstructor(const std::string& name, size_t arity)
{
  Trace("parser") << "newSortConstructor(" << name << ", " << arity << ")"
                  << std::endl;
  Sort type = d_solver->mkUninterpretedSortConstructorSort(
      arity, getNameForUserName(name));
  defineType(name, vector<Sort>(arity), type);
  return type;
}

Sort ParserState::mkUnresolvedType(const std::string& name)
{
  Sort unresolved = d_solver->mkUnresolvedDatatypeSort(name);
  defineType(name, unresolved);
  return unresolved;
}

Sort ParserState::mkUnresolvedTypeConstructor(const std::string& name,
                                              size_t arity)
{
  Sort unresolved = d_solver->mkUnresolvedDatatypeSort(name, arity);
  defineType(name, vector<Sort>(arity), unresolved);
  return unresolved;
}

Sort ParserState::mkUnresolvedTypeConstructor(const std::string& name,
                                              const std::vector<Sort>& params)
{
  Trace("parser") << "newSortConstructor(P)(" << name << ", " << params.size()
                  << ")" << std::endl;
  Sort unresolved = d_solver->mkUnresolvedDatatypeSort(name, params.size());
  defineType(name, params, unresolved);
  Sort t = getParametricSort(name, params);
  return unresolved;
}

Sort ParserState::mkUnresolvedType(const std::string& name, size_t arity)
{
  if (arity == 0)
  {
    return mkUnresolvedType(name);
  }
  return mkUnresolvedTypeConstructor(name, arity);
}

std::vector<Sort> ParserState::bindMutualDatatypeTypes(
    std::vector<DatatypeDecl>& datatypes, bool doOverload)
{
  try
  {
    std::vector<Sort> types = d_solver->mkDatatypeSorts(datatypes);

    Assert(datatypes.size() == types.size());

    for (unsigned i = 0; i < datatypes.size(); ++i)
    {
      Sort t = types[i];
      const Datatype& dt = t.getDatatype();
      const std::string& name = dt.getName();
      Trace("parser-idt") << "define " << name << " as " << t << std::endl;
      if (isDeclared(name, SYM_SORT))
      {
        throw ParserException(name + " already declared");
      }
      if (dt.isParametric())
      {
        std::vector<Sort> paramTypes = dt.getParameters();
        defineType(name, paramTypes, t);
      }
      else
      {
        defineType(name, t);
      }
      std::unordered_set<std::string> consNames;
      std::unordered_set<std::string> selNames;
      for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
      {
        const DatatypeConstructor& ctor = dt[j];
        Term constructor = ctor.getTerm();
        Trace("parser-idt") << "+ define " << constructor << std::endl;
        string constructorName = ctor.getName();
        if (consNames.find(constructorName) == consNames.end())
        {
          if (!doOverload)
          {
            checkDeclaration(constructorName, CHECK_UNDECLARED);
          }
          defineVar(constructorName, constructor, doOverload);
          consNames.insert(constructorName);
        }
        else
        {
          throw ParserException(constructorName
                                + " already declared in this datatype");
        }
        std::string testerName;
        if (getTesterName(constructor, testerName))
        {
          Term tester = ctor.getTesterTerm();
          Trace("parser-idt") << "+ define " << testerName << std::endl;
          if (!doOverload)
          {
            checkDeclaration(testerName, CHECK_UNDECLARED);
          }
          defineVar(testerName, tester, doOverload);
        }
        for (size_t k = 0, nargs = ctor.getNumSelectors(); k < nargs; k++)
        {
          const DatatypeSelector& sel = ctor[k];
          Term selector = sel.getTerm();
          Trace("parser-idt") << "+++ define " << selector << std::endl;
          string selectorName = sel.getName();
          if (selNames.find(selectorName) == selNames.end())
          {
            if (!doOverload)
            {
              checkDeclaration(selectorName, CHECK_UNDECLARED);
            }
            defineVar(selectorName, selector, doOverload);
            selNames.insert(selectorName);
          }
          else
          {
            throw ParserException(selectorName
                                  + " already declared in this datatype");
          }
        }
      }
    }
    return types;
  }
  catch (internal::IllegalArgumentException& ie)
  {
    throw ParserException(ie.getMessage());
  }
}

Sort ParserState::mkFlatFunctionType(std::vector<Sort>& sorts,
                                     Sort range,
                                     std::vector<Term>& flattenVars)
{
  if (range.isFunction())
  {
    std::vector<Sort> domainTypes = range.getFunctionDomainSorts();
    for (unsigned i = 0, size = domainTypes.size(); i < size; i++)
    {
      sorts.push_back(domainTypes[i]);
      // the introduced variable is internal (not parsable)
      std::stringstream ss;
      ss << "__flatten_var_" << i;
      Term v = d_solver->mkVar(domainTypes[i], ss.str());
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

Sort ParserState::mkFlatFunctionType(std::vector<Sort>& sorts, Sort range)
{
  if (sorts.empty())
  {
    // no difference
    return range;
  }
  if (TraceIsOn("parser"))
  {
    Trace("parser") << "mkFlatFunctionType: range " << range << " and domains ";
    for (Sort t : sorts)
    {
      Trace("parser") << " " << t;
    }
    Trace("parser") << "\n";
  }
  while (range.isFunction())
  {
    std::vector<Sort> domainTypes = range.getFunctionDomainSorts();
    sorts.insert(sorts.end(), domainTypes.begin(), domainTypes.end());
    range = range.getFunctionCodomainSort();
  }
  return d_solver->mkFunctionSort(sorts, range);
}

Term ParserState::mkHoApply(Term expr, const std::vector<Term>& args)
{
  for (unsigned i = 0; i < args.size(); i++)
  {
    expr = d_solver->mkTerm(HO_APPLY, {expr, args[i]});
  }
  return expr;
}

Term ParserState::applyTypeAscription(Term t, Sort s)
{
  Kind k = t.getKind();
  if (k == SET_EMPTY)
  {
    t = d_solver->mkEmptySet(s);
  }
  else if (k == BAG_EMPTY)
  {
    t = d_solver->mkEmptyBag(s);
  }
  else if (k == CONST_SEQUENCE)
  {
    if (!s.isSequence())
    {
      std::stringstream ss;
      ss << "Type ascription on empty sequence must be a sequence, got " << s;
      parseError(ss.str());
    }
    if (!t.getSequenceValue().empty())
    {
      std::stringstream ss;
      ss << "Cannot apply a type ascription to a non-empty sequence";
      parseError(ss.str());
    }
    t = d_solver->mkEmptySequence(s.getSequenceElementSort());
  }
  else if (k == SET_UNIVERSE)
  {
    t = d_solver->mkUniverseSet(s);
  }
  else if (k == SEP_NIL)
  {
    t = d_solver->mkSepNil(s);
  }
  else if (k == APPLY_CONSTRUCTOR)
  {
    std::vector<Term> children(t.begin(), t.end());
    // apply type ascription to the operator and reconstruct
    children[0] = applyTypeAscription(children[0], s);
    t = d_solver->mkTerm(APPLY_CONSTRUCTOR, children);
  }
  // !!! temporary until datatypes are refactored in the new API
  Sort etype = t.getSort();
  if (etype.isDatatypeConstructor())
  {
    // Type ascriptions only have an effect on the node structure if this is a
    // parametric datatype.
    // get the datatype that t belongs to
    Sort etyped = etype.getDatatypeConstructorCodomainSort();
    Datatype d = etyped.getDatatype();
    // Note that we check whether the datatype is parametric, and not whether
    // etyped is a parametric datatype, since e.g. the smt2 parser constructs
    // an arbitrary instantitated constructor term before it is resolved.
    // Hence, etyped is an instantiated datatype type, but we correctly
    // check if its datatype is parametric.
    if (d.isParametric())
    {
      // lookup by name
      DatatypeConstructor dc = d.getConstructor(t.toString());
      // ask the constructor for the specialized constructor term
      t = dc.getInstantiatedTerm(s);
    }
    // the type of t does not match the sort s by design (constructor type
    // vs datatype type), thus we use an alternative check here.
    if (t.getSort().getDatatypeConstructorCodomainSort() != s)
    {
      std::stringstream ss;
      ss << "Type ascription on constructor not satisfied, term " << t
         << " expected sort " << s << " but has sort " << etyped;
      parseError(ss.str());
    }
    return t;
  }
  // Otherwise, check that the type is correct. Type ascriptions in SMT-LIB 2.6
  // referred to the range of function sorts. Note that this is only a check
  // and does not impact the returned term.
  Sort checkSort = t.getSort();
  if (checkSort.isFunction())
  {
    checkSort = checkSort.getFunctionCodomainSort();
  }
  if (checkSort != s)
  {
    std::stringstream ss;
    ss << "Type ascription not satisfied, term " << t
       << " expected (codomain) sort " << s << " but has sort " << t.getSort();
    parseError(ss.str());
  }
  return t;
}

bool ParserState::isDeclared(const std::string& name, SymbolType type)
{
  switch (type)
  {
    case SYM_VARIABLE: return d_symtab->isBound(name);
    case SYM_SORT: return d_symtab->isBoundType(name);
    case SYM_VERBATIM: Unreachable();
  }
  Assert(false);  // Unhandled(type);
  return false;
}

void ParserState::checkDeclaration(const std::string& varName,
                                   DeclarationCheck check,
                                   SymbolType type,
                                   std::string notes)
{
  if (!d_checksEnabled)
  {
    return;
  }

  switch (check)
  {
    case CHECK_DECLARED:
      if (!isDeclared(varName, type))
      {
        parseError("Symbol '" + varName + "' not declared as a "
                   + (type == SYM_VARIABLE ? "variable" : "type")
                   + (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_UNDECLARED:
      if (isDeclared(varName, type))
      {
        parseError("Symbol '" + varName + "' previously declared as a "
                   + (type == SYM_VARIABLE ? "variable" : "type")
                   + (notes.size() == 0 ? notes : "\n" + notes));
      }
      break;

    case CHECK_NONE: break;

    default: Assert(false);  // Unhandled(check);
  }
}

void ParserState::checkFunctionLike(Term fun)
{
  if (d_checksEnabled && !isFunctionLike(fun))
  {
    stringstream ss;
    ss << "Expecting function-like symbol, found '";
    ss << fun;
    ss << "'";
    parseError(ss.str());
  }
}

void ParserState::addOperator(Kind kind) { d_logicOperators.insert(kind); }

void ParserState::warning(const std::string& msg) { d_psc->warning(msg); }

void ParserState::parseError(const std::string& msg) { d_psc->parseError(msg); }

void ParserState::unexpectedEOF(const std::string& msg)
{
  d_psc->unexpectedEOF(msg);
}

void ParserState::preemptCommand(Command* cmd) { d_psc->preemptCommand(cmd); }

void ParserState::attributeNotSupported(const std::string& attr)
{
  if (d_attributesWarnedAbout.find(attr) == d_attributesWarnedAbout.end())
  {
    stringstream ss;
    ss << "warning: Attribute '" << attr
       << "' not supported (ignoring this and all following uses)";
    warning(ss.str());
    d_attributesWarnedAbout.insert(attr);
  }
}

size_t ParserState::scopeLevel() const { return d_symman->scopeLevel(); }

void ParserState::pushScope(bool isUserContext)
{
  d_symman->pushScope(isUserContext);
}

void ParserState::pushGetValueScope()
{
  pushScope();
  // We cannot ask for the model domain elements if we are in parse-only mode.
  // Hence, we do nothing here.
  if (d_parseOnly)
  {
    return;
  }
  // we must bind all relevant uninterpreted constants, which coincide with
  // the set of uninterpreted constants that are printed in the definition
  // of a model.
  std::vector<Sort> declareSorts = d_symman->getModelDeclareSorts();
  Trace("parser") << "Push get value scope, with " << declareSorts.size()
                  << " declared sorts" << std::endl;
  for (const Sort& s : declareSorts)
  {
    std::vector<Term> elements = d_solver->getModelDomainElements(s);
    Trace("parser") << "elements for " << s << ":" << std::endl;
    for (const Term& e : elements)
    {
      Trace("parser") << "  " << e.getKind() << " " << e << std::endl;
      if (e.getKind() == Kind::UNINTERPRETED_SORT_VALUE)
      {
        defineVar(e.getUninterpretedSortValue(), e);
      }
      else
      {
        Assert(false)
            << "model domain element is not an uninterpreted sort value: " << e;
      }
    }
  }
}

void ParserState::popScope() { d_symman->popScope(); }

void ParserState::reset() {}

SymbolManager* ParserState::getSymbolManager() { return d_symman; }

std::wstring ParserState::processAdHocStringEsc(const std::string& s)
{
  std::wstring ws;
  {
    std::setlocale(LC_ALL, "en_US.utf8");
    std::mbtowc(nullptr, nullptr, 0);
    const char* end = s.data() + s.size();
    const char* ptr = s.data();
    for (wchar_t c; ptr != end;)
    {
      int res = std::mbtowc(&c, ptr, end - ptr);
      if (res == -1)
      {
        std::cerr << "Invalid escape sequence in " << s << std::endl;
        break;
      }
      else if (res == 0)
      {
        break;
      }
      else
      {
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

std::string ParserState::stripQuotes(const std::string& s)
{
  if (s.size() < 2 || s[0] != '\"' || s[s.size() - 1] != '\"')
  {
    parseError("Expected a string delimited by quotes, got invalid string `" + s
               + "`.");
  }
  return s.substr(1, s.size() - 2);
}

Term ParserState::mkCharConstant(const std::string& s)
{
  Assert(s.find_first_not_of("0123456789abcdefABCDEF", 0) == std::string::npos
         && s.size() <= 5 && s.size() > 0)
      << "Unexpected string for hexadecimal character " << s;
  wchar_t val = static_cast<wchar_t>(std::stoul(s, 0, 16));
  return d_solver->mkString(std::wstring(1, val));
}

uint32_t stringToUnsigned(const std::string& str)
{
  uint32_t result;
  std::stringstream ss;
  ss << str;
  ss >> result;
  return result;
}

}  // namespace parser
}  // namespace cvc5

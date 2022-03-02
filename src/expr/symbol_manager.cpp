/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The symbol manager.
 */

#include "expr/symbol_manager.h"

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"

using namespace cvc5::context;

namespace cvc5 {

// ---------------------------------------------- SymbolManager::Implementation

class SymbolManager::Implementation
{
  using TermStringMap = CDHashMap<api::Term, std::string, std::hash<api::Term>>;
  using TermSet = CDHashSet<api::Term, std::hash<api::Term>>;
  using SortList = CDList<api::Sort>;
  using TermList = CDList<api::Term>;

 public:
  Implementation()
      : d_context(),
        d_names(&d_context),
        d_namedAsserts(&d_context),
        d_declareSorts(&d_context),
        d_declareTerms(&d_context),
        d_funToSynth(&d_context),
        d_hasPushedScope(&d_context, false),
        d_lastSynthName(&d_context)
  {
    // use an outermost push, to be able to clear all definitions
    d_context.push();
  }

  ~Implementation() { d_context.pop(); }
  /** set expression name */
  NamingResult setExpressionName(api::Term t,
                                 const std::string& name,
                                 bool isAssertion = false);
  /** get expression name */
  bool getExpressionName(api::Term t,
                         std::string& name,
                         bool isAssertion = false) const;
  /** get expression names */
  void getExpressionNames(const std::vector<api::Term>& ts,
                          std::vector<std::string>& names,
                          bool areAssertions = false) const;
  /** get expression names */
  std::map<api::Term, std::string> getExpressionNames(bool areAssertions) const;
  /** get model declare sorts */
  std::vector<api::Sort> getModelDeclareSorts() const;
  /** get model declare terms */
  std::vector<api::Term> getModelDeclareTerms() const;
  /** get functions to synthesize */
  std::vector<api::Term> getFunctionsToSynthesize() const;
  /** Add declared sort to the list of model declarations. */
  void addModelDeclarationSort(api::Sort s);
  /** Add declared term to the list of model declarations. */
  void addModelDeclarationTerm(api::Term t);
  /** Add function to the list of functions to synthesize. */
  void addFunctionToSynthesize(api::Term t);
  /** reset */
  void reset();
  /** reset assertions */
  void resetAssertions();
  /** Push a scope in the expression names. */
  void pushScope(bool isUserContext);
  /** Pop a scope in the expression names. */
  void popScope();
  /** Have we pushed a scope (e.g. let or quantifier) in the current context? */
  bool hasPushedScope() const;
  /** Set the last abduct-to-synthesize had the given name. */
  void setLastSynthName(const std::string& name);
  /** Get the name of the last abduct-to-synthesize */
  const std::string& getLastSynthName() const;

 private:
  /** The context manager for the scope maps. */
  Context d_context;
  /** Map terms to names */
  TermStringMap d_names;
  /** The set of terms with assertion names */
  TermSet d_namedAsserts;
  /** Declared sorts (for model printing) */
  SortList d_declareSorts;
  /** Declared terms (for model printing) */
  TermList d_declareTerms;
  /** Functions to synthesize (for response to check-synth) */
  TermList d_funToSynth;
  /**
   * Have we pushed a scope (e.g. a let or quantifier) in the current context?
   */
  CDO<bool> d_hasPushedScope;
  /** The last abduct or interpolant to synthesize name */
  CDO<std::string> d_lastSynthName;
};

NamingResult SymbolManager::Implementation::setExpressionName(
    api::Term t, const std::string& name, bool isAssertion)
{
  Trace("sym-manager") << "SymbolManager: set expression name: " << t << " -> "
                       << name << ", isAssertion=" << isAssertion << std::endl;
  if (d_hasPushedScope.get())
  {
    // cannot name subexpressions under binders
    return NamingResult::ERROR_IN_BINDER;
  }

  if (isAssertion)
  {
    d_namedAsserts.insert(t);
  }
  if (d_names.find(t) != d_names.end())
  {
    // already named assertion
    return NamingResult::ERROR_ALREADY_NAMED;
  }
  d_names[t] = name;
  return NamingResult::SUCCESS;
}

bool SymbolManager::Implementation::getExpressionName(api::Term t,
                                                      std::string& name,
                                                      bool isAssertion) const
{
  TermStringMap::const_iterator it = d_names.find(t);
  if (it == d_names.end())
  {
    return false;
  }
  if (isAssertion)
  {
    // must be an assertion name
    if (d_namedAsserts.find(t) == d_namedAsserts.end())
    {
      return false;
    }
  }
  name = (*it).second;
  return true;
}

void SymbolManager::Implementation::getExpressionNames(
    const std::vector<api::Term>& ts,
    std::vector<std::string>& names,
    bool areAssertions) const
{
  for (const api::Term& t : ts)
  {
    std::string name;
    if (getExpressionName(t, name, areAssertions))
    {
      names.push_back(name);
    }
  }
}

std::map<api::Term, std::string>
SymbolManager::Implementation::getExpressionNames(bool areAssertions) const
{
  std::map<api::Term, std::string> emap;
  for (TermStringMap::const_iterator it = d_names.begin(),
                                     itend = d_names.end();
       it != itend;
       ++it)
  {
    api::Term t = (*it).first;
    if (areAssertions && d_namedAsserts.find(t) == d_namedAsserts.end())
    {
      continue;
    }
    emap[t] = (*it).second;
  }
  return emap;
}

std::vector<api::Sort> SymbolManager::Implementation::getModelDeclareSorts()
    const
{
  std::vector<api::Sort> declareSorts(d_declareSorts.begin(),
                                      d_declareSorts.end());
  return declareSorts;
}

std::vector<api::Term> SymbolManager::Implementation::getModelDeclareTerms()
    const
{
  std::vector<api::Term> declareTerms(d_declareTerms.begin(),
                                      d_declareTerms.end());
  return declareTerms;
}

std::vector<api::Term> SymbolManager::Implementation::getFunctionsToSynthesize()
    const
{
  return std::vector<api::Term>(d_funToSynth.begin(), d_funToSynth.end());
}

void SymbolManager::Implementation::addModelDeclarationSort(api::Sort s)
{
  Trace("sym-manager") << "SymbolManager: addModelDeclarationSort " << s
                       << std::endl;
  d_declareSorts.push_back(s);
}

void SymbolManager::Implementation::addModelDeclarationTerm(api::Term t)
{
  Trace("sym-manager") << "SymbolManager: addModelDeclarationTerm " << t
                       << std::endl;
  d_declareTerms.push_back(t);
}

void SymbolManager::Implementation::addFunctionToSynthesize(api::Term f)
{
  Trace("sym-manager") << "SymbolManager: addFunctionToSynthesize " << f
                       << std::endl;
  d_funToSynth.push_back(f);
}

void SymbolManager::Implementation::pushScope(bool isUserContext)
{
  Trace("sym-manager") << "SymbolManager: pushScope, isUserContext = "
                       << isUserContext << std::endl;
  PrettyCheckArgument(!d_hasPushedScope.get() || !isUserContext,
                      "cannot push a user context within a scope context");
  d_context.push();
  if (!isUserContext)
  {
    d_hasPushedScope = true;
  }
}

void SymbolManager::Implementation::popScope()
{
  Trace("sym-manager") << "SymbolManager: popScope" << std::endl;
  if (d_context.getLevel() == 0)
  {
    throw ScopeException();
  }
  d_context.pop();
  Trace("sym-manager-debug")
      << "d_hasPushedScope is now " << d_hasPushedScope.get() << std::endl;
}

bool SymbolManager::Implementation::hasPushedScope() const
{
  return d_hasPushedScope.get();
}

void SymbolManager::Implementation::setLastSynthName(const std::string& name)
{
  d_lastSynthName = name;
}

const std::string& SymbolManager::Implementation::getLastSynthName() const
{
  return d_lastSynthName.get();
}

void SymbolManager::Implementation::reset()
{
  Trace("sym-manager") << "SymbolManager: reset" << std::endl;
  // clear names by popping to context level 0
  while (d_context.getLevel() > 0)
  {
    d_context.pop();
  }
  // push the outermost context
  d_context.push();
}

void SymbolManager::Implementation::resetAssertions()
{
  Trace("sym-manager") << "SymbolManager: resetAssertions" << std::endl;
  // clear names by popping to context level 1
  while (d_context.getLevel() > 1)
  {
    d_context.pop();
  }
}

// ---------------------------------------------- SymbolManager

SymbolManager::SymbolManager(api::Solver* s)
    : d_solver(s),
      d_implementation(new SymbolManager::Implementation()),
      d_globalDeclarations(false)
{
}

SymbolManager::~SymbolManager() {}

SymbolTable* SymbolManager::getSymbolTable() { return &d_symtabAllocated; }

NamingResult SymbolManager::setExpressionName(api::Term t,
                                              const std::string& name,
                                              bool isAssertion)
{
  return d_implementation->setExpressionName(t, name, isAssertion);
}

bool SymbolManager::getExpressionName(api::Term t,
                                      std::string& name,
                                      bool isAssertion) const
{
  return d_implementation->getExpressionName(t, name, isAssertion);
}

void SymbolManager::getExpressionNames(const std::vector<api::Term>& ts,
                                       std::vector<std::string>& names,
                                       bool areAssertions) const
{
  return d_implementation->getExpressionNames(ts, names, areAssertions);
}

std::map<api::Term, std::string> SymbolManager::getExpressionNames(
    bool areAssertions) const
{
  return d_implementation->getExpressionNames(areAssertions);
}
std::vector<api::Sort> SymbolManager::getModelDeclareSorts() const
{
  return d_implementation->getModelDeclareSorts();
}
std::vector<api::Term> SymbolManager::getModelDeclareTerms() const
{
  return d_implementation->getModelDeclareTerms();
}

std::vector<api::Term> SymbolManager::getFunctionsToSynthesize() const
{
  return d_implementation->getFunctionsToSynthesize();
}

void SymbolManager::addModelDeclarationSort(api::Sort s)
{
  d_implementation->addModelDeclarationSort(s);
}

void SymbolManager::addModelDeclarationTerm(api::Term t)
{
  d_implementation->addModelDeclarationTerm(t);
}

void SymbolManager::addFunctionToSynthesize(api::Term f)
{
  d_implementation->addFunctionToSynthesize(f);
}

size_t SymbolManager::scopeLevel() const
{
  return d_symtabAllocated.getLevel();
}

void SymbolManager::pushScope(bool isUserContext)
{
  // we do not push user contexts when global declarations is true. This
  // policy applies both to the symbol table and to the symbol manager.
  if (d_globalDeclarations && isUserContext)
  {
    return;
  }
  d_implementation->pushScope(isUserContext);
  d_symtabAllocated.pushScope();
}

void SymbolManager::popScope()
{
  // If global declarations is true, then if d_hasPushedScope is false, then
  // the pop corresponds to a user context, which we did not push. Note this
  // additionally relies on the fact that user contexts cannot be pushed
  // within scope contexts. Hence, since we did not push the context, we
  // do not pop a context here.
  if (d_globalDeclarations && !d_implementation->hasPushedScope())
  {
    return;
  }
  d_symtabAllocated.popScope();
  d_implementation->popScope();
}

void SymbolManager::setGlobalDeclarations(bool flag)
{
  d_globalDeclarations = flag;
}

bool SymbolManager::getGlobalDeclarations() const
{
  return d_globalDeclarations;
}

void SymbolManager::setLastSynthName(const std::string& name)
{
  d_implementation->setLastSynthName(name);
}

const std::string& SymbolManager::getLastSynthName() const
{
  return d_implementation->getLastSynthName();
}

void SymbolManager::reset()
{
  // reset resets the symbol table even when global declarations are true
  d_symtabAllocated.reset();
  d_implementation->reset();
}

void SymbolManager::resetAssertions()
{
  d_implementation->resetAssertions();
  if (!d_globalDeclarations)
  {
    d_symtabAllocated.resetAssertions();
  }
}

}  // namespace cvc5

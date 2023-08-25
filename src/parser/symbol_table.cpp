/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Convenience class for scoping variable and type declarations
 * (implementation).
 */

#include "parser/symbol_table.h"

#include <cvc5/cvc5.h>

#include <ostream>
#include <string>
#include <unordered_map>
#include <utility>

#include "base/check.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"

namespace cvc5::internal::parser {

using context::CDHashMap;
using context::CDHashSet;
using context::Context;
using std::copy;
using std::endl;
using std::ostream_iterator;
using std::pair;
using std::string;
using std::vector;

/** Overloaded type trie.
 *
 * This data structure stores a trie of expressions with
 * the same name, and must be distinguished by their argument types.
 * It is context-dependent.
 *
 * Using the argument allowFunVariants,
 * it may either be configured to allow function variants or not,
 * where a function variant is function that expects the same
 * argument types as another.
 *
 * For example, the following definitions introduce function
 * variants for the symbol f:
 *
 * 1. (declare-fun f (Int) Int) and
 *    (declare-fun f (Int) Bool)
 *
 * 2. (declare-fun f (Int) Int) and
 *    (declare-fun f (Int) Int)
 *
 * 3. (declare-datatypes ((Tup 0)) ((f (data Int)))) and
 *    (declare-fun f (Int) Tup)
 *
 * 4. (declare-datatypes ((Tup 0)) ((mkTup (f Int)))) and
 *    (declare-fun f (Tup) Bool)
 *
 * If function variants is set to true, we allow function variants
 * but not function redefinition. In examples 2 and 3, f is
 * declared twice as a symbol of identical argument and range
 * types. We never accept these definitions. However, we do
 * allow examples 1 and 4 above when allowFunVariants is true.
 *
 * For 0-argument functions (constants), we always allow
 * function variants.  That is, we always accept these examples:
 *
 * 5.  (declare-fun c () Int)
 *     (declare-fun c () Bool)
 *
 * 6.  (declare-datatypes ((Enum 0)) ((c)))
 *     (declare-fun c () Int)
 *
 * and always reject constant redefinition such as:
 *
 * 7. (declare-fun c () Int)
 *    (declare-fun c () Int)
 *
 * 8. (declare-datatypes ((Enum 0)) ((c))) and
 *    (declare-fun c () Enum)
 */
class OverloadedTypeTrie
{
 public:
  OverloadedTypeTrie(Context* c, bool allowFunVariants = false)
      : d_overloaded_symbols(new (true) CDHashSet<Term, std::hash<Term>>(c)),
        d_allowFunctionVariants(allowFunVariants)
  {
  }
  ~OverloadedTypeTrie() { d_overloaded_symbols->deleteSelf(); }

  /** is this function overloaded? */
  bool isOverloadedFunction(Term fun) const;

  /** Get overloaded constant for type.
   * If possible, it returns a defined symbol with name
   * that has type t. Otherwise returns null expression.
   */
  Term getOverloadedConstantForType(const std::string& name, Sort t) const;

  /**
   * If possible, returns a defined function for a name
   * and a vector of expected argument types. Otherwise returns
   * null expression.
   */
  Term getOverloadedFunctionForTypes(const std::string& name,
                                     const std::vector<Sort>& argTypes) const;
  /** called when obj is bound to name, and prev_bound_obj was already bound to
   * name Returns false if the binding is invalid.
   */
  bool bind(const string& name, Term prev_bound_obj, Term obj);

 private:
  /** Marks expression obj with name as overloaded.
   * Adds relevant information to the type arg trie data structure.
   * It returns false if there is already an expression bound to that name
   * whose type expects the same arguments as the type of obj but is not
   * identical to the type of obj.  For example, if we declare :
   *
   * (declare-datatypes () ((List (cons (hd Int) (tl List)) (nil))))
   * (declare-fun cons (Int List) List)
   *
   * cons : constructor_type( Int, List, List )
   * cons : function_type( Int, List, List )
   *
   * These are put in the same place in the trie but do not have identical type,
   * hence we return false.
   */
  bool markOverloaded(const string& name, Term obj);
  /** the null expression */
  Term d_nullTerm;
  // The (context-independent) trie storing that maps expected argument
  // vectors to symbols. All expressions stored in d_symbols are only
  // interpreted as active if they also appear in the context-dependent
  // set d_overloaded_symbols.
  class TypeArgTrie
  {
   public:
    // children of this node
    std::map<Sort, TypeArgTrie> d_children;
    // symbols at this node
    std::map<Sort, Term> d_symbols;
  };
  /** for each string with operator overloading, this stores the data structure
   * above. */
  std::unordered_map<std::string, TypeArgTrie> d_overload_type_arg_trie;
  /** The set of overloaded symbols. */
  CDHashSet<Term, std::hash<Term>>* d_overloaded_symbols;
  /** allow function variants
   * This is true if we allow overloading (non-constant) functions that expect
   * the same argument types.
   */
  bool d_allowFunctionVariants;
  /** get unique overloaded function
   * If tat->d_symbols contains an active overloaded function, it
   * returns that function, where that function must be unique
   * if reqUnique=true.
   * Otherwise, it returns the null expression.
   */
  Term getOverloadedFunctionAt(const TypeArgTrie* tat,
                               bool reqUnique = true) const;
};

bool OverloadedTypeTrie::isOverloadedFunction(Term fun) const
{
  return d_overloaded_symbols->find(fun) != d_overloaded_symbols->end();
}

Term OverloadedTypeTrie::getOverloadedConstantForType(const std::string& name,
                                                      Sort t) const
{
  std::unordered_map<std::string, TypeArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end())
  {
    std::map<Sort, Term>::const_iterator its = it->second.d_symbols.find(t);
    if (its != it->second.d_symbols.end())
    {
      Term expr = its->second;
      // must be an active symbol
      if (isOverloadedFunction(expr))
      {
        return expr;
      }
    }
  }
  return d_nullTerm;
}

Term OverloadedTypeTrie::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Sort>& argTypes) const
{
  std::unordered_map<std::string, TypeArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end())
  {
    const TypeArgTrie* tat = &it->second;
    for (unsigned i = 0; i < argTypes.size(); i++)
    {
      std::map<Sort, TypeArgTrie>::const_iterator itc =
          tat->d_children.find(argTypes[i]);
      if (itc != tat->d_children.end())
      {
        tat = &itc->second;
      }
      else
      {
        Trace("parser-overloading")
            << "Could not find overloaded function " << name << std::endl;

        // no functions match
        return d_nullTerm;
      }
    }
    // we ensure that there is *only* one active symbol at this node
    return getOverloadedFunctionAt(tat);
  }
  return d_nullTerm;
}

bool OverloadedTypeTrie::bind(const string& name, Term prev_bound_obj, Term obj)
{
  Assert(prev_bound_obj != obj);
  bool retprev = true;
  if (!isOverloadedFunction(prev_bound_obj))
  {
    // mark previous as overloaded
    retprev = markOverloaded(name, prev_bound_obj);
  }
  // mark this as overloaded
  bool retobj = markOverloaded(name, obj);
  return retprev && retobj;
}

bool OverloadedTypeTrie::markOverloaded(const string& name, Term obj)
{
  Trace("parser-overloading") << "Overloaded function : " << name;
  Trace("parser-overloading")
      << " with type " << obj.getSort() << ", obj is " << obj << std::endl;
  // get the argument types
  Sort t = obj.getSort();
  Sort rangeType = t;
  std::vector<Sort> argTypes;
  if (t.isFunction())
  {
    argTypes = t.getFunctionDomainSorts();
    rangeType = t.getFunctionCodomainSort();
  }
  else if (t.isDatatypeConstructor())
  {
    argTypes = t.getDatatypeConstructorDomainSorts();
    rangeType = t.getDatatypeConstructorCodomainSort();
  }
  else if (t.isDatatypeSelector())
  {
    argTypes.push_back(t.getDatatypeSelectorDomainSort());
    rangeType = t.getDatatypeSelectorCodomainSort();
  }
  // add to the trie
  TypeArgTrie* tat = &d_overload_type_arg_trie[name];
  for (unsigned i = 0; i < argTypes.size(); i++)
  {
    tat = &(tat->d_children[argTypes[i]]);
  }

  // check if function variants are allowed here
  if (d_allowFunctionVariants || argTypes.empty())
  {
    // they are allowed, check for redefinition
    std::map<Sort, Term>::iterator it = tat->d_symbols.find(rangeType);
    if (it != tat->d_symbols.end())
    {
      Term prev_obj = it->second;
      // if there is already an active function with the same name and expects
      // the same argument types and has the same return type, we reject the
      // re-declaration here.
      if (isOverloadedFunction(prev_obj))
      {
        Trace("parser-overloading") << "...existing overload" << std::endl;
        return false;
      }
    }
  }
  else
  {
    // they are not allowed, we cannot have any function defined here.
    Term existingFun = getOverloadedFunctionAt(tat, false);
    if (!existingFun.isNull())
    {
      Trace("parser-overloading")
          << "...existing fun (no variant)" << std::endl;
      return false;
    }
  }
  Trace("parser-overloading") << "...update symbols" << std::endl;

  // otherwise, update the symbols
  d_overloaded_symbols->insert(obj);
  tat->d_symbols[rangeType] = obj;
  return true;
}

Term OverloadedTypeTrie::getOverloadedFunctionAt(
    const OverloadedTypeTrie::TypeArgTrie* tat, bool reqUnique) const
{
  Term retExpr;
  for (std::map<Sort, Term>::const_iterator its = tat->d_symbols.begin();
       its != tat->d_symbols.end();
       ++its)
  {
    Term expr = its->second;
    if (isOverloadedFunction(expr))
    {
      if (retExpr.isNull())
      {
        if (!reqUnique)
        {
          return expr;
        }
        else
        {
          retExpr = expr;
        }
      }
      else
      {
        // multiple functions match
        return d_nullTerm;
      }
    }
  }
  return retExpr;
}

class SymbolTable::Implementation
{
 public:
  Implementation()
      : d_context(),
        d_exprMap(&d_context),
        d_typeMap(&d_context),
        d_overload_trie(&d_context)
  {
  }

  ~Implementation() {}

  bool bind(const string& name, Term obj, bool doOverload);
  void bindType(const string& name, Sort t);
  void bindType(const string& name, const vector<Sort>& params, Sort t);
  bool isBound(const string& name) const;
  bool isBoundType(const string& name) const;
  Term lookup(const string& name) const;
  Sort lookupType(const string& name) const;
  Sort lookupType(const string& name, const vector<Sort>& params) const;
  size_t lookupArity(const string& name);
  void popScope();
  void pushScope();
  size_t getLevel() const;
  void reset();
  void resetAssertions();
  //------------------------ operator overloading
  /** implementation of function from header */
  bool isOverloadedFunction(Term fun) const;

  /** implementation of function from header */
  Term getOverloadedConstantForType(const std::string& name, Sort t) const;

  /** implementation of function from header */
  Term getOverloadedFunctionForTypes(const std::string& name,
                                     const std::vector<Sort>& argTypes) const;
  //------------------------ end operator overloading
 private:
  /** The context manager for the scope maps. */
  Context d_context;

  /** A map for expressions. */
  CDHashMap<string, Term> d_exprMap;

  /** A map for types. */
  using TypeMap = CDHashMap<string, std::pair<vector<Sort>, Sort>>;
  TypeMap d_typeMap;

  //------------------------ operator overloading
  /** the null term */
  Term d_nullTerm;
  /** The null sort */
  Sort d_nullSort;
  // overloaded type trie, stores all information regarding overloading
  OverloadedTypeTrie d_overload_trie;
  /** bind with overloading
   * This is called whenever obj is bound to name where overloading symbols is
   * allowed. If a symbol is previously bound to that name, it marks both as
   * overloaded. Returns false if the binding was invalid.
   */
  bool bindWithOverloading(const string& name, Term obj);
  //------------------------ end operator overloading
}; /* SymbolTable::Implementation */

bool SymbolTable::Implementation::bind(const string& name,
                                       Term obj,
                                       bool doOverload)
{
  Assert(!obj.isNull()) << "cannot bind to a null Term";
  Trace("sym-table") << "SymbolTable: bind " << name << " to " << obj
                     << ", doOverload=" << doOverload << std::endl;
  if (doOverload)
  {
    if (!bindWithOverloading(name, obj))
    {
      return false;
    }
  }
  d_exprMap.insert(name, obj);

  return true;
}

bool SymbolTable::Implementation::isBound(const string& name) const
{
  return d_exprMap.find(name) != d_exprMap.end();
}

Term SymbolTable::Implementation::lookup(const string& name) const
{
  CDHashMap<string, Term>::const_iterator it = d_exprMap.find(name);
  if (it == d_exprMap.end())
  {
    return d_nullTerm;
  }
  Term expr = it->second;
  if (isOverloadedFunction(expr))
  {
    return d_nullTerm;
  }
  return expr;
}

void SymbolTable::Implementation::bindType(const string& name, Sort t)
{
  d_typeMap.insert(name, make_pair(vector<Sort>(), t));
}

void SymbolTable::Implementation::bindType(const string& name,
                                           const vector<Sort>& params,
                                           Sort t)
{
  if (TraceIsOn("sort"))
  {
    Trace("sort") << "bindType(" << name << ", [";
    if (params.size() > 0)
    {
      copy(params.begin(),
           params.end() - 1,
           ostream_iterator<Sort>(Trace("sort"), ", "));
      Trace("sort") << params.back();
    }
    Trace("sort") << "], " << t << ")" << endl;
  }

  d_typeMap.insert(name, make_pair(params, t));
}

bool SymbolTable::Implementation::isBoundType(const string& name) const
{
  return d_typeMap.find(name) != d_typeMap.end();
}

Sort SymbolTable::Implementation::lookupType(const string& name) const
{
  TypeMap::const_iterator it = d_typeMap.find(name);
  if (it == d_typeMap.end())
  {
    return d_nullSort;
  }
  std::pair<std::vector<Sort>, Sort> p = it->second;
  if (p.first.size() != 0)
  {
    std::stringstream ss;
    ss << "type constructor arity is wrong: `" << name << "' requires "
       << p.first.size() << " parameters but was provided 0";
    throw Exception(ss.str());
  }
  return p.second;
}

Sort SymbolTable::Implementation::lookupType(const string& name,
                                             const vector<Sort>& params) const
{
  TypeMap::const_iterator it = d_typeMap.find(name);
  if (it == d_typeMap.end())
  {
    return d_nullSort;
  }
  std::pair<std::vector<Sort>, Sort> p = it->second;
  if (p.first.size() != params.size())
  {
    std::stringstream ss;
    ss << "type constructor arity is wrong: `" << name.c_str() << "' requires "
       << p.first.size() << " parameters but was provided " << params.size();
    throw Exception(ss.str());
  }
  if (p.first.size() == 0)
  {
    Assert(p.second.isUninterpretedSort());
    return p.second;
  }
  if (p.second.isDatatype())
  {
    Assert(p.second.getDatatype().isParametric())
        << "expected parametric datatype";
    return p.second.instantiate(params);
  }
  bool isUninterpretedSortConstructor =
      p.second.isUninterpretedSortConstructor();
  if (TraceIsOn("sort"))
  {
    Trace("sort") << "instantiating using a sort "
                  << (isUninterpretedSortConstructor ? "constructor"
                                                     : "substitution")
                  << std::endl;
    Trace("sort") << "have formals [";
    copy(p.first.begin(),
         p.first.end() - 1,
         ostream_iterator<Sort>(Trace("sort"), ", "));
    Trace("sort") << p.first.back() << "]" << std::endl << "parameters   [";
    copy(params.begin(),
         params.end() - 1,
         ostream_iterator<Sort>(Trace("sort"), ", "));
    Trace("sort") << params.back() << "]" << endl
                  << "type ctor    " << name << std::endl
                  << "type is      " << p.second << std::endl;
  }
  Sort instantiation = isUninterpretedSortConstructor
                           ? p.second.instantiate(params)
                           : p.second.substitute(p.first, params);
  Trace("sort") << "instance is  " << instantiation << std::endl;

  return instantiation;
}

size_t SymbolTable::Implementation::lookupArity(const string& name)
{
  std::pair<std::vector<Sort>, Sort> p = (*d_typeMap.find(name)).second;
  return p.first.size();
}

void SymbolTable::Implementation::popScope()
{
  // should not pop beyond level one
  if (d_context.getLevel() == 0)
  {
    throw ScopeException();
  }
  d_context.pop();
}

void SymbolTable::Implementation::pushScope() { d_context.push(); }

size_t SymbolTable::Implementation::getLevel() const
{
  return d_context.getLevel();
}

void SymbolTable::Implementation::reset()
{
  Trace("sym-table") << "SymbolTable: reset" << std::endl;
  this->SymbolTable::Implementation::~Implementation();
  new (this) SymbolTable::Implementation();
}

void SymbolTable::Implementation::resetAssertions()
{
  Trace("sym-table") << "SymbolTable: resetAssertions" << std::endl;
  // pop all contexts
  while (d_context.getLevel() > 0)
  {
    d_context.pop();
  }
  d_context.push();
}

bool SymbolTable::Implementation::isOverloadedFunction(Term fun) const
{
  return d_overload_trie.isOverloadedFunction(fun);
}

Term SymbolTable::Implementation::getOverloadedConstantForType(
    const std::string& name, Sort t) const
{
  return d_overload_trie.getOverloadedConstantForType(name, t);
}

Term SymbolTable::Implementation::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Sort>& argTypes) const
{
  return d_overload_trie.getOverloadedFunctionForTypes(name, argTypes);
}

bool SymbolTable::Implementation::bindWithOverloading(const string& name,
                                                      Term obj)
{
  CDHashMap<string, Term>::const_iterator it = d_exprMap.find(name);
  if (it != d_exprMap.end())
  {
    const Term& prev_bound_obj = (*it).second;
    if (prev_bound_obj != obj)
    {
      return d_overload_trie.bind(name, prev_bound_obj, obj);
    }
  }
  return true;
}

bool SymbolTable::isOverloadedFunction(Term fun) const
{
  return d_implementation->isOverloadedFunction(fun);
}

Term SymbolTable::getOverloadedConstantForType(const std::string& name,
                                               Sort t) const
{
  return d_implementation->getOverloadedConstantForType(name, t);
}

Term SymbolTable::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Sort>& argTypes) const
{
  return d_implementation->getOverloadedFunctionForTypes(name, argTypes);
}

SymbolTable::SymbolTable() : d_implementation(new SymbolTable::Implementation())
{
}

SymbolTable::~SymbolTable() {}
bool SymbolTable::bind(const string& name, Term obj, bool doOverload)
{
  return d_implementation->bind(name, obj, doOverload);
}

void SymbolTable::bindType(const string& name, Sort t)
{
  d_implementation->bindType(name, t);
}

void SymbolTable::bindType(const string& name,
                           const vector<Sort>& params,
                           Sort t)
{
  d_implementation->bindType(name, params, t);
}

bool SymbolTable::isBound(const string& name) const
{
  return d_implementation->isBound(name);
}
bool SymbolTable::isBoundType(const string& name) const
{
  return d_implementation->isBoundType(name);
}
Term SymbolTable::lookup(const string& name) const
{
  return d_implementation->lookup(name);
}
Sort SymbolTable::lookupType(const string& name) const
{
  return d_implementation->lookupType(name);
}

Sort SymbolTable::lookupType(const string& name,
                             const vector<Sort>& params) const
{
  return d_implementation->lookupType(name, params);
}
size_t SymbolTable::lookupArity(const string& name)
{
  return d_implementation->lookupArity(name);
}
void SymbolTable::popScope() { d_implementation->popScope(); }
void SymbolTable::pushScope() { d_implementation->pushScope(); }
size_t SymbolTable::getLevel() const { return d_implementation->getLevel(); }
void SymbolTable::reset() { d_implementation->reset(); }
void SymbolTable::resetAssertions() { d_implementation->resetAssertions(); }

}  // namespace cvc5::internal::parser

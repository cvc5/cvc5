/*********************                                                        */
/*! \file symbol_table.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type
 ** declarations (implementation)
 **
 ** Convenience class for scoping variable and type declarations
 ** (implementation).
 **/

#include "expr/symbol_table.h"

#include <ostream>
#include <string>
#include <unordered_map>
#include <utility>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "expr/dtype.h"
#include "expr/expr.h"
#include "expr/expr_manager_scope.h"
#include "expr/type.h"

namespace CVC4 {

using ::CVC4::context::CDHashMap;
using ::CVC4::context::CDHashSet;
using ::CVC4::context::Context;
using ::std::copy;
using ::std::endl;
using ::std::ostream_iterator;
using ::std::pair;
using ::std::string;
using ::std::vector;

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
class OverloadedSortTrie {
 public:
  OverloadedSortTrie(Context* c, bool allowFunVariants = false)
      : d_overloaded_symbols(new (true) CDHashSet<Term, TermHashFunction>(c)),
        d_allowFunctionVariants(allowFunVariants)
  {
  }
  ~OverloadedSortTrie() { d_overloaded_symbols->deleteSelf(); }

  /** is this function overloaded? */
  bool isOverloadedFunction(Term fun) const;

  /** Get overloaded constant for type.
   * If possible, it returns a defined symbol with name
   * that has type t. Otherwise returns null expression.
   */
  Term getOverloadedConstantForSort(const std::string& name, Sort t) const;

  /**
   * If possible, returns a defined function for a name
   * and a vector of expected argument types. Otherwise returns
   * null expression.
   */
  Term getOverloadedFunctionForSorts(const std::string& name,
                                     const std::vector<Sort>& argSorts) const;
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
  class SortArgTrie {
   public:
    // children of this node
    std::map<Sort, SortArgTrie> d_children;
    // symbols at this node
    std::map<Sort, Term> d_symbols;
  };
  /** for each string with operator overloading, this stores the data structure
   * above. */
  std::unordered_map<std::string, SortArgTrie> d_overload_type_arg_trie;
  /** The set of overloaded symbols. */
  CDHashSet<Term, TermHashFunction>* d_overloaded_symbols;
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
  Term getOverloadedFunctionAt(const SortArgTrie* tat, bool reqUnique=true) const;
};

bool OverloadedSortTrie::isOverloadedFunction(Term fun) const {
  return d_overloaded_symbols->find(fun) != d_overloaded_symbols->end();
}

Term OverloadedSortTrie::getOverloadedConstantForSort(const std::string& name,
                                                      Sort t) const {
  std::unordered_map<std::string, SortArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end()) {
    std::map<Sort, Term>::const_iterator its = it->second.d_symbols.find(t);
    if (its != it->second.d_symbols.end()) {
      Term expr = its->second;
      // must be an active symbol
      if (isOverloadedFunction(expr)) {
        return expr;
      }
    }
  }
  return d_nullTerm;
}

Term OverloadedSortTrie::getOverloadedFunctionForSorts(
    const std::string& name, const std::vector<Sort>& argSorts) const {
  std::unordered_map<std::string, SortArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end()) {
    const SortArgTrie* tat = &it->second;
    for (unsigned i = 0; i < argSorts.size(); i++) {
      std::map<Sort, SortArgTrie>::const_iterator itc =
          tat->d_children.find(argSorts[i]);
      if (itc != tat->d_children.end()) {
        tat = &itc->second;
      } else {
        Trace("parser-overloading")
            << "Could not find overloaded function " << name << std::endl;
        // it may be a parametric datatype
        SortNode tna = SortNode::fromSort(argSorts[i]);
        if (tna.isParametricDatatype())
        {
          Trace("parser-overloading")
              << "Parametric overloaded datatype selector " << name << " "
              << tna << std::endl;
          const DSort& dt = SortNode::fromSort(argSorts[i]).getDSort();
          // tng is the "generalized" version of the instantiated parametric
          // type tna
          Sort tng = dt.getSortNode().toSort();
          itc = tat->d_children.find(tng);
          if (itc != tat->d_children.end())
          {
            tat = &itc->second;
          }
        }
        if (tat == nullptr)
        {
          // no functions match
          return d_nullTerm;
        }
      }
    }
    // we ensure that there is *only* one active symbol at this node
    return getOverloadedFunctionAt(tat);
  }
  return d_nullTerm;
}

bool OverloadedSortTrie::bind(const string& name, Term prev_bound_obj,
                              Term obj) {
  bool retprev = true;
  if (!isOverloadedFunction(prev_bound_obj)) {
    // mark previous as overloaded
    retprev = markOverloaded(name, prev_bound_obj);
  }
  // mark this as overloaded
  bool retobj = markOverloaded(name, obj);
  return retprev && retobj;
}

bool OverloadedSortTrie::markOverloaded(const string& name, Term obj) {
  Trace("parser-overloading") << "Overloaded function : " << name;
  Trace("parser-overloading") << " with type " << obj.getSort() << std::endl;
  // get the argument types
  Sort t = obj.getSort();
  Sort rangeSort = t;
  std::vector<Sort> argSorts;
  if (t.isFunction()) {
    argSorts = static_cast<FunctionSort>(t).getArgSorts();
    rangeSort = static_cast<FunctionSort>(t).getRangeSort();
  } else if (t.isConstructor()) {
    argSorts = static_cast<ConstructorSort>(t).getArgSorts();
    rangeSort = static_cast<ConstructorSort>(t).getRangeSort();
  } else if (t.isTester()) {
    argSorts.push_back(static_cast<TesterSort>(t).getDomain());
    rangeSort = static_cast<TesterSort>(t).getRangeSort();
  } else if (t.isSelector()) {
    argSorts.push_back(static_cast<SelectorSort>(t).getDomain());
    rangeSort = static_cast<SelectorSort>(t).getRangeSort();
  }
  // add to the trie
  SortArgTrie* tat = &d_overload_type_arg_trie[name];
  for (unsigned i = 0; i < argSorts.size(); i++) {
    tat = &(tat->d_children[argSorts[i]]);
  }

  // check if function variants are allowed here
  if (d_allowFunctionVariants || argSorts.empty())
  {
    // they are allowed, check for redefinition
    std::map<Sort, Term>::iterator it = tat->d_symbols.find(rangeSort);
    if (it != tat->d_symbols.end())
    {
      Term prev_obj = it->second;
      // if there is already an active function with the same name and expects
      // the same argument types and has the same return type, we reject the 
      // re-declaration here.
      if (isOverloadedFunction(prev_obj))
      {
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
      return false;
    }
  }

  // otherwise, update the symbols
  d_overloaded_symbols->insert(obj);
  tat->d_symbols[rangeSort] = obj;
  return true;
}

Term OverloadedSortTrie::getOverloadedFunctionAt(
    const OverloadedSortTrie::SortArgTrie* tat, bool reqUnique) const
{
  Term retTerm;
  for (std::map<Sort, Term>::const_iterator its = tat->d_symbols.begin();
       its != tat->d_symbols.end();
       ++its)
  {
    Term expr = its->second;
    if (isOverloadedFunction(expr))
    {
      if (retTerm.isNull())
      {
        if (!reqUnique) 
        {
          return expr;
        }
        else 
        {
          retTerm = expr;
        }
      }
      else
      {
        // multiple functions match
        return d_nullTerm;
      }
    }
  }
  return retTerm;
}

class SymbolTable::Implementation {
 public:
  Implementation()
      : d_context(),
        d_exprMap(new (true) CDHashMap<string, Term>(&d_context)),
        d_typeMap(new (true) SortMap(&d_context))
  {
    d_overload_trie = new OverloadedSortTrie(&d_context);
  }

  ~Implementation() {
    d_exprMap->deleteSelf();
    d_typeMap->deleteSelf();
    delete d_overload_trie;
  }

  bool bind(const string& name, Term obj, bool levelZero, bool doOverload);
  void bindSort(const string& name, Sort t, bool levelZero = false);
  void bindSort(const string& name, const vector<Sort>& params, Sort t,
                bool levelZero = false);
  bool isBound(const string& name) const;
  bool isBoundSort(const string& name) const;
  Term lookup(const string& name) const;
  Sort lookupSort(const string& name) const;
  Sort lookupSort(const string& name, const vector<Sort>& params) const;
  size_t lookupArity(const string& name);
  void popScope();
  void pushScope();
  size_t getLevel() const;
  void reset();
  //------------------------ operator overloading
  /** implementation of function from header */
  bool isOverloadedFunction(Term fun) const;

  /** implementation of function from header */
  Term getOverloadedConstantForSort(const std::string& name, Sort t) const;

  /** implementation of function from header */
  Term getOverloadedFunctionForSorts(const std::string& name,
                                     const std::vector<Sort>& argSorts) const;
  //------------------------ end operator overloading
 private:
  /** The context manager for the scope maps. */
  Context d_context;

  /** A map for expressions. */
  CDHashMap<string, Term>* d_exprMap;

  /** A map for types. */
  using SortMap = CDHashMap<string, std::pair<vector<Sort>, Sort>>;
  SortMap* d_typeMap;

  //------------------------ operator overloading
  // the null expression
  Term d_nullTerm;
  // overloaded type trie, stores all information regarding overloading
  OverloadedSortTrie* d_overload_trie;
  /** bind with overloading
   * This is called whenever obj is bound to name where overloading symbols is
   * allowed. If a symbol is previously bound to that name, it marks both as
   * overloaded. Returns false if the binding was invalid.
   */
  bool bindWithOverloading(const string& name, Term obj);
  //------------------------ end operator overloading
}; /* SymbolTable::Implementation */

bool SymbolTable::Implementation::bind(const string& name, Term obj,
                                       bool levelZero, bool doOverload) {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Term");
  TermManagerScope ems(obj);
  if (doOverload) {
    if (!bindWithOverloading(name, obj)) {
      return false;
    }
  }
  if (levelZero) {
    d_exprMap->insertAtContextLevelZero(name, obj);
  } else {
    d_exprMap->insert(name, obj);
  }
  return true;
}

bool SymbolTable::Implementation::isBound(const string& name) const {
  return d_exprMap->find(name) != d_exprMap->end();
}

Term SymbolTable::Implementation::lookup(const string& name) const {
  Assert(isBound(name));
  Term expr = (*d_exprMap->find(name)).second;
  if (isOverloadedFunction(expr)) {
    return d_nullTerm;
  } else {
    return expr;
  }
}

void SymbolTable::Implementation::bindSort(const string& name, Sort t,
                                           bool levelZero) {
  if (levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(vector<Sort>(), t));
  } else {
    d_typeMap->insert(name, make_pair(vector<Sort>(), t));
  }
}

void SymbolTable::Implementation::bindSort(const string& name,
                                           const vector<Sort>& params, Sort t,
                                           bool levelZero) {
  if (Debug.isOn("sort")) {
    Debug("sort") << "bindSort(" << name << ", [";
    if (params.size() > 0) {
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Sort>(Debug("sort"), ", "));
      Debug("sort") << params.back();
    }
    Debug("sort") << "], " << t << ")" << endl;
  }
  if (levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(params, t));
  } else {
    d_typeMap->insert(name, make_pair(params, t));
  }
}

bool SymbolTable::Implementation::isBoundSort(const string& name) const {
  return d_typeMap->find(name) != d_typeMap->end();
}

Sort SymbolTable::Implementation::lookupSort(const string& name) const {
  pair<vector<Sort>, Sort> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == 0, name,
                      "type constructor arity is wrong: "
                      "`%s' requires %u parameters but was provided 0",
                      name.c_str(), p.first.size());
  return p.second;
}

Sort SymbolTable::Implementation::lookupSort(const string& name,
                                             const vector<Sort>& params) const {
  pair<vector<Sort>, Sort> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == params.size(), params,
                      "type constructor arity is wrong: "
                      "`%s' requires %u parameters but was provided %u",
                      name.c_str(), p.first.size(), params.size());
  if (p.first.size() == 0) {
    PrettyCheckArgument(p.second.isSort(), name.c_str());
    return p.second;
  }
  if (p.second.isSortConstructor()) {
    if (Debug.isOn("sort")) {
      Debug("sort") << "instantiating using a sort constructor" << endl;
      Debug("sort") << "have formals [";
      copy(p.first.begin(), p.first.end() - 1,
           ostream_iterator<Sort>(Debug("sort"), ", "));
      Debug("sort") << p.first.back() << "]" << endl << "parameters   [";
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Sort>(Debug("sort"), ", "));
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Sort instantiation = SortConstructorSort(p.second).instantiate(params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  } else if (p.second.isDatatype()) {
    PrettyCheckArgument(DatatypeSort(p.second).isParametric(), name,
                        "expected parametric datatype");
    return DatatypeSort(p.second).instantiate(params);
  } else {
    if (Debug.isOn("sort")) {
      Debug("sort") << "instantiating using a sort substitution" << endl;
      Debug("sort") << "have formals [";
      copy(p.first.begin(), p.first.end() - 1,
           ostream_iterator<Sort>(Debug("sort"), ", "));
      Debug("sort") << p.first.back() << "]" << endl << "parameters   [";
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Sort>(Debug("sort"), ", "));
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Sort instantiation = p.second.substitute(p.first, params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  }
}

size_t SymbolTable::Implementation::lookupArity(const string& name) {
  pair<vector<Sort>, Sort> p = (*d_typeMap->find(name)).second;
  return p.first.size();
}

void SymbolTable::Implementation::popScope() {
  if (d_context.getLevel() == 0) {
    throw ScopeException();
  }
  d_context.pop();
}

void SymbolTable::Implementation::pushScope() { d_context.push(); }

size_t SymbolTable::Implementation::getLevel() const {
  return d_context.getLevel();
}

void SymbolTable::Implementation::reset() {
  this->SymbolTable::Implementation::~Implementation();
  new (this) SymbolTable::Implementation();
}

bool SymbolTable::Implementation::isOverloadedFunction(Term fun) const {
  return d_overload_trie->isOverloadedFunction(fun);
}

Term SymbolTable::Implementation::getOverloadedConstantForSort(
    const std::string& name, Sort t) const {
  return d_overload_trie->getOverloadedConstantForSort(name, t);
}

Term SymbolTable::Implementation::getOverloadedFunctionForSorts(
    const std::string& name, const std::vector<Sort>& argSorts) const {
  return d_overload_trie->getOverloadedFunctionForSorts(name, argSorts);
}

bool SymbolTable::Implementation::bindWithOverloading(const string& name,
                                                      Term obj) {
  CDHashMap<string, Term>::const_iterator it = d_exprMap->find(name);
  if (it != d_exprMap->end()) {
    const Term& prev_bound_obj = (*it).second;
    if (prev_bound_obj != obj) {
      return d_overload_trie->bind(name, prev_bound_obj, obj);
    }
  }
  return true;
}

bool SymbolTable::isOverloadedFunction(Term fun) const {
  return d_implementation->isOverloadedFunction(fun);
}

Term SymbolTable::getOverloadedConstantForSort(const std::string& name,
                                               Sort t) const {
  return d_implementation->getOverloadedConstantForSort(name, t);
}

Term SymbolTable::getOverloadedFunctionForSorts(
    const std::string& name, const std::vector<Sort>& argSorts) const {
  return d_implementation->getOverloadedFunctionForSorts(name, argSorts);
}

SymbolTable::SymbolTable()
    : d_implementation(new SymbolTable::Implementation()) {}

SymbolTable::~SymbolTable() {}
bool SymbolTable::bind(const string& name,
                       Term obj,
                       bool levelZero,
                       bool doOverload)
{
  return d_implementation->bind(name, obj, levelZero, doOverload);
}

void SymbolTable::bindSort(const string& name, Sort t, bool levelZero)
{
  d_implementation->bindSort(name, t, levelZero);
}

void SymbolTable::bindSort(const string& name,
                           const vector<Sort>& params,
                           Sort t,
                           bool levelZero)
{
  d_implementation->bindSort(name, params, t, levelZero);
}

bool SymbolTable::isBound(const string& name) const
{
  return d_implementation->isBound(name);
}
bool SymbolTable::isBoundSort(const string& name) const
{
  return d_implementation->isBoundSort(name);
}
Term SymbolTable::lookup(const string& name) const
{
  return d_implementation->lookup(name);
}
Sort SymbolTable::lookupSort(const string& name) const
{
  return d_implementation->lookupSort(name);
}

Sort SymbolTable::lookupSort(const string& name,
                             const vector<Sort>& params) const
{
  return d_implementation->lookupSort(name, params);
}
size_t SymbolTable::lookupArity(const string& name) {
  return d_implementation->lookupArity(name);
}
void SymbolTable::popScope() { d_implementation->popScope(); }
void SymbolTable::pushScope() { d_implementation->pushScope(); }
size_t SymbolTable::getLevel() const { return d_implementation->getLevel(); }
void SymbolTable::reset() { d_implementation->reset(); }

}  // namespace CVC4

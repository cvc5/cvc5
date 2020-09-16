/*********************                                                        */
/*! \file symbol_table.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
class OverloadedTypeTrie {
 public:
  OverloadedTypeTrie(Context* c, bool allowFunVariants = false)
      : d_overloaded_symbols(new (true) CDHashSet<Expr, ExprHashFunction>(c)),
        d_allowFunctionVariants(allowFunVariants)
  {
  }
  ~OverloadedTypeTrie() { d_overloaded_symbols->deleteSelf(); }

  /** is this function overloaded? */
  bool isOverloadedFunction(Expr fun) const;

  /** Get overloaded constant for type.
   * If possible, it returns a defined symbol with name
   * that has type t. Otherwise returns null expression.
   */
  Expr getOverloadedConstantForType(const std::string& name, Type t) const;

  /**
   * If possible, returns a defined function for a name
   * and a vector of expected argument types. Otherwise returns
   * null expression.
   */
  Expr getOverloadedFunctionForTypes(const std::string& name,
                                     const std::vector<Type>& argTypes) const;
  /** called when obj is bound to name, and prev_bound_obj was already bound to
   * name Returns false if the binding is invalid.
   */
  bool bind(const string& name, Expr prev_bound_obj, Expr obj);

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
  bool markOverloaded(const string& name, Expr obj);
  /** the null expression */
  Expr d_nullExpr;
  // The (context-independent) trie storing that maps expected argument
  // vectors to symbols. All expressions stored in d_symbols are only
  // interpreted as active if they also appear in the context-dependent
  // set d_overloaded_symbols.
  class TypeArgTrie {
   public:
    // children of this node
    std::map<Type, TypeArgTrie> d_children;
    // symbols at this node
    std::map<Type, Expr> d_symbols;
  };
  /** for each string with operator overloading, this stores the data structure
   * above. */
  std::unordered_map<std::string, TypeArgTrie> d_overload_type_arg_trie;
  /** The set of overloaded symbols. */
  CDHashSet<Expr, ExprHashFunction>* d_overloaded_symbols;
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
  Expr getOverloadedFunctionAt(const TypeArgTrie* tat, bool reqUnique=true) const;
};

bool OverloadedTypeTrie::isOverloadedFunction(Expr fun) const {
  return d_overloaded_symbols->find(fun) != d_overloaded_symbols->end();
}

Expr OverloadedTypeTrie::getOverloadedConstantForType(const std::string& name,
                                                      Type t) const {
  std::unordered_map<std::string, TypeArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end()) {
    std::map<Type, Expr>::const_iterator its = it->second.d_symbols.find(t);
    if (its != it->second.d_symbols.end()) {
      Expr expr = its->second;
      // must be an active symbol
      if (isOverloadedFunction(expr)) {
        return expr;
      }
    }
  }
  return d_nullExpr;
}

Expr OverloadedTypeTrie::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Type>& argTypes) const {
  std::unordered_map<std::string, TypeArgTrie>::const_iterator it =
      d_overload_type_arg_trie.find(name);
  if (it != d_overload_type_arg_trie.end()) {
    const TypeArgTrie* tat = &it->second;
    for (unsigned i = 0; i < argTypes.size(); i++) {
      std::map<Type, TypeArgTrie>::const_iterator itc =
          tat->d_children.find(argTypes[i]);
      if (itc != tat->d_children.end()) {
        tat = &itc->second;
      } else {
        Trace("parser-overloading")
            << "Could not find overloaded function " << name << std::endl;
        // it may be a parametric datatype
        TypeNode tna = TypeNode::fromType(argTypes[i]);
        if (tna.isParametricDatatype())
        {
          Trace("parser-overloading")
              << "Parametric overloaded datatype selector " << name << " "
              << tna << std::endl;
          const DType& dt = TypeNode::fromType(argTypes[i]).getDType();
          // tng is the "generalized" version of the instantiated parametric
          // type tna
          Type tng = dt.getTypeNode().toType();
          itc = tat->d_children.find(tng);
          if (itc != tat->d_children.end())
          {
            tat = &itc->second;
          }
        }
        if (tat == nullptr)
        {
          // no functions match
          return d_nullExpr;
        }
      }
    }
    // we ensure that there is *only* one active symbol at this node
    return getOverloadedFunctionAt(tat);
  }
  return d_nullExpr;
}

bool OverloadedTypeTrie::bind(const string& name, Expr prev_bound_obj,
                              Expr obj) {
  bool retprev = true;
  if (!isOverloadedFunction(prev_bound_obj)) {
    // mark previous as overloaded
    retprev = markOverloaded(name, prev_bound_obj);
  }
  // mark this as overloaded
  bool retobj = markOverloaded(name, obj);
  return retprev && retobj;
}

bool OverloadedTypeTrie::markOverloaded(const string& name, Expr obj) {
  Trace("parser-overloading") << "Overloaded function : " << name;
  Trace("parser-overloading") << " with type " << obj.getType() << std::endl;
  // get the argument types
  Type t = obj.getType();
  Type rangeType = t;
  std::vector<Type> argTypes;
  if (t.isFunction()) {
    argTypes = static_cast<FunctionType>(t).getArgTypes();
    rangeType = static_cast<FunctionType>(t).getRangeType();
  } else if (t.isConstructor()) {
    argTypes = static_cast<ConstructorType>(t).getArgTypes();
    rangeType = static_cast<ConstructorType>(t).getRangeType();
  } else if (t.isTester()) {
    argTypes.push_back(static_cast<TesterType>(t).getDomain());
    rangeType = static_cast<TesterType>(t).getRangeType();
  } else if (t.isSelector()) {
    argTypes.push_back(static_cast<SelectorType>(t).getDomain());
    rangeType = static_cast<SelectorType>(t).getRangeType();
  }
  // add to the trie
  TypeArgTrie* tat = &d_overload_type_arg_trie[name];
  for (unsigned i = 0; i < argTypes.size(); i++) {
    tat = &(tat->d_children[argTypes[i]]);
  }

  // check if function variants are allowed here
  if (d_allowFunctionVariants || argTypes.empty())
  {
    // they are allowed, check for redefinition
    std::map<Type, Expr>::iterator it = tat->d_symbols.find(rangeType);
    if (it != tat->d_symbols.end())
    {
      Expr prev_obj = it->second;
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
    Expr existingFun = getOverloadedFunctionAt(tat, false);
    if (!existingFun.isNull())
    {
      return false;
    }
  }

  // otherwise, update the symbols
  d_overloaded_symbols->insert(obj);
  tat->d_symbols[rangeType] = obj;
  return true;
}

Expr OverloadedTypeTrie::getOverloadedFunctionAt(
    const OverloadedTypeTrie::TypeArgTrie* tat, bool reqUnique) const
{
  Expr retExpr;
  for (std::map<Type, Expr>::const_iterator its = tat->d_symbols.begin();
       its != tat->d_symbols.end();
       ++its)
  {
    Expr expr = its->second;
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
        return d_nullExpr;
      }
    }
  }
  return retExpr;
}

class SymbolTable::Implementation {
 public:
  Implementation()
      : d_context(),
        d_exprMap(new (true) CDHashMap<string, Expr>(&d_context)),
        d_typeMap(new (true) TypeMap(&d_context))
  {
    d_overload_trie = new OverloadedTypeTrie(&d_context);
  }

  ~Implementation() {
    d_exprMap->deleteSelf();
    d_typeMap->deleteSelf();
    delete d_overload_trie;
  }

  bool bind(const string& name, Expr obj, bool levelZero, bool doOverload);
  void bindType(const string& name, Type t, bool levelZero = false);
  void bindType(const string& name, const vector<Type>& params, Type t,
                bool levelZero = false);
  bool isBound(const string& name) const;
  bool isBoundType(const string& name) const;
  Expr lookup(const string& name) const;
  Type lookupType(const string& name) const;
  Type lookupType(const string& name, const vector<Type>& params) const;
  size_t lookupArity(const string& name);
  void popScope();
  void pushScope();
  size_t getLevel() const;
  void reset();
  //------------------------ operator overloading
  /** implementation of function from header */
  bool isOverloadedFunction(Expr fun) const;

  /** implementation of function from header */
  Expr getOverloadedConstantForType(const std::string& name, Type t) const;

  /** implementation of function from header */
  Expr getOverloadedFunctionForTypes(const std::string& name,
                                     const std::vector<Type>& argTypes) const;
  //------------------------ end operator overloading
 private:
  /** The context manager for the scope maps. */
  Context d_context;

  /** A map for expressions. */
  CDHashMap<string, Expr>* d_exprMap;

  /** A map for types. */
  using TypeMap = CDHashMap<string, std::pair<vector<Type>, Type>>;
  TypeMap* d_typeMap;

  //------------------------ operator overloading
  // the null expression
  Expr d_nullExpr;
  // overloaded type trie, stores all information regarding overloading
  OverloadedTypeTrie* d_overload_trie;
  /** bind with overloading
   * This is called whenever obj is bound to name where overloading symbols is
   * allowed. If a symbol is previously bound to that name, it marks both as
   * overloaded. Returns false if the binding was invalid.
   */
  bool bindWithOverloading(const string& name, Expr obj);
  //------------------------ end operator overloading
}; /* SymbolTable::Implementation */

bool SymbolTable::Implementation::bind(const string& name, Expr obj,
                                       bool levelZero, bool doOverload) {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
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

Expr SymbolTable::Implementation::lookup(const string& name) const {
  Assert(isBound(name));
  Expr expr = (*d_exprMap->find(name)).second;
  if (isOverloadedFunction(expr)) {
    return d_nullExpr;
  } else {
    return expr;
  }
}

void SymbolTable::Implementation::bindType(const string& name, Type t,
                                           bool levelZero) {
  if (levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(vector<Type>(), t));
  } else {
    d_typeMap->insert(name, make_pair(vector<Type>(), t));
  }
}

void SymbolTable::Implementation::bindType(const string& name,
                                           const vector<Type>& params, Type t,
                                           bool levelZero) {
  if (Debug.isOn("sort")) {
    Debug("sort") << "bindType(" << name << ", [";
    if (params.size() > 0) {
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Type>(Debug("sort"), ", "));
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

bool SymbolTable::Implementation::isBoundType(const string& name) const {
  return d_typeMap->find(name) != d_typeMap->end();
}

Type SymbolTable::Implementation::lookupType(const string& name) const {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == 0, name,
                      "type constructor arity is wrong: "
                      "`%s' requires %u parameters but was provided 0",
                      name.c_str(), p.first.size());
  return p.second;
}

Type SymbolTable::Implementation::lookupType(const string& name,
                                             const vector<Type>& params) const {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
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
           ostream_iterator<Type>(Debug("sort"), ", "));
      Debug("sort") << p.first.back() << "]" << endl << "parameters   [";
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Type>(Debug("sort"), ", "));
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Type instantiation = SortConstructorType(p.second).instantiate(params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  } else if (p.second.isDatatype()) {
    PrettyCheckArgument(DatatypeType(p.second).isParametric(), name,
                        "expected parametric datatype");
    return DatatypeType(p.second).instantiate(params);
  } else {
    if (Debug.isOn("sort")) {
      Debug("sort") << "instantiating using a sort substitution" << endl;
      Debug("sort") << "have formals [";
      copy(p.first.begin(), p.first.end() - 1,
           ostream_iterator<Type>(Debug("sort"), ", "));
      Debug("sort") << p.first.back() << "]" << endl << "parameters   [";
      copy(params.begin(), params.end() - 1,
           ostream_iterator<Type>(Debug("sort"), ", "));
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Type instantiation = p.second.substitute(p.first, params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  }
}

size_t SymbolTable::Implementation::lookupArity(const string& name) {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
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

bool SymbolTable::Implementation::isOverloadedFunction(Expr fun) const {
  return d_overload_trie->isOverloadedFunction(fun);
}

Expr SymbolTable::Implementation::getOverloadedConstantForType(
    const std::string& name, Type t) const {
  return d_overload_trie->getOverloadedConstantForType(name, t);
}

Expr SymbolTable::Implementation::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Type>& argTypes) const {
  return d_overload_trie->getOverloadedFunctionForTypes(name, argTypes);
}

bool SymbolTable::Implementation::bindWithOverloading(const string& name,
                                                      Expr obj) {
  CDHashMap<string, Expr>::const_iterator it = d_exprMap->find(name);
  if (it != d_exprMap->end()) {
    const Expr& prev_bound_obj = (*it).second;
    if (prev_bound_obj != obj) {
      return d_overload_trie->bind(name, prev_bound_obj, obj);
    }
  }
  return true;
}

bool SymbolTable::isOverloadedFunction(Expr fun) const {
  return d_implementation->isOverloadedFunction(fun);
}

Expr SymbolTable::getOverloadedConstantForType(const std::string& name,
                                               Type t) const {
  return d_implementation->getOverloadedConstantForType(name, t);
}

Expr SymbolTable::getOverloadedFunctionForTypes(
    const std::string& name, const std::vector<Type>& argTypes) const {
  return d_implementation->getOverloadedFunctionForTypes(name, argTypes);
}

SymbolTable::SymbolTable()
    : d_implementation(new SymbolTable::Implementation()) {}

SymbolTable::~SymbolTable() {}
bool SymbolTable::bind(const string& name,
                       Expr obj,
                       bool levelZero,
                       bool doOverload)
{
  return d_implementation->bind(name, obj, levelZero, doOverload);
}

void SymbolTable::bindType(const string& name, Type t, bool levelZero)
{
  d_implementation->bindType(name, t, levelZero);
}

void SymbolTable::bindType(const string& name,
                           const vector<Type>& params,
                           Type t,
                           bool levelZero)
{
  d_implementation->bindType(name, params, t, levelZero);
}

bool SymbolTable::isBound(const string& name) const
{
  return d_implementation->isBound(name);
}
bool SymbolTable::isBoundType(const string& name) const
{
  return d_implementation->isBoundType(name);
}
Expr SymbolTable::lookup(const string& name) const
{
  return d_implementation->lookup(name);
}
Type SymbolTable::lookupType(const string& name) const
{
  return d_implementation->lookupType(name);
}

Type SymbolTable::lookupType(const string& name,
                             const vector<Type>& params) const
{
  return d_implementation->lookupType(name, params);
}
size_t SymbolTable::lookupArity(const string& name) {
  return d_implementation->lookupArity(name);
}
void SymbolTable::popScope() { d_implementation->popScope(); }
void SymbolTable::pushScope() { d_implementation->pushScope(); }
size_t SymbolTable::getLevel() const { return d_implementation->getLevel(); }
void SymbolTable::reset() { d_implementation->reset(); }

}  // namespace CVC4

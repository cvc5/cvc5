/*********************                                                        */
/*! \file symbol_table.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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
#include <utility>
#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"
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

// This data structure stores a trie of expressions with
// the same name, and must be distinguished by their argument types.
// It is context-dependent.
class OverloadedTypeTrie
{
public:
  OverloadedTypeTrie(Context * c ) :
    d_overloaded_symbols(new (true) CDHashSet<Expr, ExprHashFunction>(c)) {
  }  
  ~OverloadedTypeTrie() {
    d_overloaded_symbols->deleteSelf();
  }
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
  Expr getOverloadedFunctionForTypes(const std::string& name, const std::vector< Type >& argTypes) const;
  /** called when obj is bound to name, and prev_bound_obj was already bound to name */
  void bind(const string& name, Expr prev_bound_obj, Expr obj);
private:
  /** Marks expression obj with name as overloaded. 
   * Adds relevant information to the type arg trie data structure.
  */
  void markOverloaded(const string& name, Expr obj);
  /** the null expression */
  Expr d_nullExpr;
  // The (context-independent) trie storing that maps expected argument
  // vectors to symbols. All expressions stored in d_symbols are only 
  // interpreted as active if they also appear in the context-dependent
  // set d_overloaded_symbols.
  class TypeArgTrie {
  public:
    // children of this node
    std::map< Type, TypeArgTrie > d_children;
    // symbols at this node
    std::map< Type, Expr > d_symbols;
  };
  /** for each string with operator overloading, this stores the data structure above. */
  std::unordered_map< std::string, TypeArgTrie > d_overload_type_arg_trie;
  /** The set of overloaded symbols. */
  CDHashSet<Expr, ExprHashFunction>* d_overloaded_symbols;
};

bool OverloadedTypeTrie::isOverloadedFunction(Expr fun) const {
  return d_overloaded_symbols->find(fun)!=d_overloaded_symbols->end();
}

Expr OverloadedTypeTrie::getOverloadedConstantForType(const std::string& name, Type t) const {
  std::unordered_map< std::string, TypeArgTrie >::const_iterator it = d_overload_type_arg_trie.find(name);
  if(it!=d_overload_type_arg_trie.end()) {
    std::map< Type, Expr >::const_iterator its = it->second.d_symbols.find(t);
    if(its!=it->second.d_symbols.end()) {
      // must be an active symbol
      Expr expr = its->second;
      if(isOverloadedFunction(expr)) {
        return expr;
      }
    }
  }
  return d_nullExpr;
}

Expr OverloadedTypeTrie::getOverloadedFunctionForTypes(const std::string& name, 
                                                       const std::vector< Type >& argTypes) const {
  std::unordered_map< std::string, TypeArgTrie >::const_iterator it = d_overload_type_arg_trie.find(name);
  if(it!=d_overload_type_arg_trie.end()) {
    const TypeArgTrie * tat = &it->second;
    for(unsigned i=0; i<argTypes.size(); i++) {
      std::map< Type, TypeArgTrie >::const_iterator itc = tat->d_children.find(argTypes[i]);
      if(itc!=tat->d_children.end()) {
        tat = &itc->second;
      }else{
        // no functions match 
        return d_nullExpr;
      }
    }
    // now, we must ensure that there is *only* one active symbol at this node
    Expr retExpr;
    for(std::map< Type, Expr >::const_iterator its = tat->d_symbols.begin(); its != tat->d_symbols.end(); ++its) {
      Expr expr = its->second;
      if(isOverloadedFunction(expr)) {
        if(retExpr.isNull()) {
          retExpr = expr;
        }else{
          // multiple functions match
          return d_nullExpr;
        }
      }
    }
    return retExpr;
  }
  return d_nullExpr;
}

void OverloadedTypeTrie::bind(const string& name, Expr prev_bound_obj, Expr obj) {
  if(!isOverloadedFunction(prev_bound_obj)) {
    // mark previous as overloaded
    markOverloaded(name, prev_bound_obj);
  }
  // mark this as overloaded
  markOverloaded(name, obj);
}

void OverloadedTypeTrie::markOverloaded(const string& name, Expr obj) {
  Trace("parser-overloading") << "Overloaded function : " << name;
  Trace("parser-overloading") << " with type " << obj.getType() << std::endl;
  // get the argument types
  Type t = obj.getType();
  Type rangeType = t;
  std::vector< Type > argTypes;
  if(t.isFunction()) {
    argTypes = static_cast<FunctionType>(t).getArgTypes();
    rangeType = static_cast<FunctionType>(t).getRangeType();
  }else if(t.isConstructor()) {
    argTypes = static_cast<ConstructorType>(t).getArgTypes();
    rangeType = static_cast<ConstructorType>(t).getRangeType();
  }else if(t.isTester()) {
    argTypes.push_back( static_cast<TesterType>(t).getDomain() );
    rangeType = static_cast<TesterType>(t).getRangeType();
  }else if(t.isSelector()) {
    argTypes.push_back( static_cast<SelectorType>(t).getDomain() );
    rangeType = static_cast<SelectorType>(t).getRangeType();
  }
  // add to the trie
  TypeArgTrie * tat = &d_overload_type_arg_trie[name];
  for(unsigned i=0; i<argTypes.size(); i++) {
    tat = &(tat->d_children[argTypes[i]]);
  }
  
  std::map< Type, Expr >::iterator it = d_symbols.find( rangeType );
  if( it!=d_symbols.end() ){
    // if there is already an active function with the same name and an identical type, simply ignore it
    if( isOverloadedFunction( it->second ) ){
      return;
    }
  }
  
  // otherwise, update the symbols
  d_overloaded_symbols->insert(obj);
  tat->d_symbols[rangeType] = obj;
}


class SymbolTable::Implementation {
 public:
  Implementation()
      : d_context(),
        d_exprMap(new (true) CDHashMap<string, Expr>(&d_context)),
        d_typeMap(new (true) TypeMap(&d_context)),
        d_functions(new (true) CDHashSet<Expr, ExprHashFunction>(&d_context)){
    d_overload_trie = new OverloadedTypeTrie(&d_context);
  }

  ~Implementation() {
    d_exprMap->deleteSelf();
    d_typeMap->deleteSelf();
    d_functions->deleteSelf();
    delete d_overload_trie;
  }

  void bind(const string& name, Expr obj, bool levelZero, bool doOverload) throw();
  void bindDefinedFunction(const string& name, Expr obj,
                           bool levelZero, bool doOverload) throw();
  void bindType(const string& name, Type t, bool levelZero = false) throw();
  void bindType(const string& name, const vector<Type>& params, Type t,
                bool levelZero = false) throw();
  bool isBound(const string& name) const throw();
  bool isBoundDefinedFunction(const string& name) const throw();
  bool isBoundDefinedFunction(Expr func) const throw();
  bool isBoundType(const string& name) const throw();
  Expr lookup(const string& name) const throw();
  Type lookupType(const string& name) const throw();
  Type lookupType(const string& name, const vector<Type>& params) const throw();
  size_t lookupArity(const string& name);
  void popScope() throw(ScopeException);
  void pushScope() throw();
  size_t getLevel() const throw();
  void reset();
  //------------------------ operator overloading
  /** implementation of function from header */
  bool isOverloadedFunction(Expr fun) const;
  
  /** implementation of function from header */
  Expr getOverloadedConstantForType(const std::string& name, Type t) const;
  
  /** implementation of function from header */
  Expr getOverloadedFunctionForTypes(const std::string& name, const std::vector< Type >& argTypes) const;
  //------------------------ end operator overloading
 private:
  /** The context manager for the scope maps. */
  Context d_context;

  /** A map for expressions. */
  CDHashMap<string, Expr>* d_exprMap;

  /** A map for types. */
  using TypeMap = CDHashMap<string, std::pair<vector<Type>, Type>>;
  TypeMap* d_typeMap;

  /** A set of defined functions. */
  CDHashSet<Expr, ExprHashFunction>* d_functions;
  
  //------------------------ operator overloading
  // the null expression
  Expr d_nullExpr;
  // overloaded type trie, stores all information regarding overloading
  OverloadedTypeTrie * d_overload_trie;
  /** bind with overloading
   * This is called whenever obj is bound to name where overloading symbols is allowed.
   * If a symbol is previously bound to that name, it marks both as overloaded.
  */
  void bindWithOverloading(const string& name, Expr obj);
  //------------------------ end operator overloading
}; /* SymbolTable::Implementation */

void SymbolTable::Implementation::bind(const string& name, Expr obj,
                                       bool levelZero, bool doOverload) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  if (doOverload) {
    bindWithOverloading(name, obj);
  }
  if (levelZero) {
    d_exprMap->insertAtContextLevelZero(name, obj);
  } else {
    d_exprMap->insert(name, obj);
  }
}

void SymbolTable::Implementation::bindDefinedFunction(const string& name,
                                                      Expr obj,
                                                      bool levelZero, 
                                                      bool doOverload) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  if (doOverload) {
    bindWithOverloading(name, obj);
  }
  if (levelZero) {
    d_exprMap->insertAtContextLevelZero(name, obj);
    d_functions->insertAtContextLevelZero(obj);
  } else {
    d_exprMap->insert(name, obj);
    d_functions->insert(obj);
  }
}

bool SymbolTable::Implementation::isBound(const string& name) const throw() {
  return d_exprMap->find(name) != d_exprMap->end();
}

bool SymbolTable::Implementation::isBoundDefinedFunction(
    const string& name) const throw() {
  CDHashMap<string, Expr>::iterator found = d_exprMap->find(name);
  return found != d_exprMap->end() && d_functions->contains((*found).second);
}

bool SymbolTable::Implementation::isBoundDefinedFunction(Expr func) const
    throw() {
  return d_functions->contains(func);
}

Expr SymbolTable::Implementation::lookup(const string& name) const throw() {
  Expr expr = (*d_exprMap->find(name)).second;
  if(isOverloadedFunction(expr)) {
    return d_nullExpr;
  }else{
    return expr;
  }
}

void SymbolTable::Implementation::bindType(const string& name, Type t,
                                           bool levelZero) throw() {
  if (levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(vector<Type>(), t));
  } else {
    d_typeMap->insert(name, make_pair(vector<Type>(), t));
  }
}

void SymbolTable::Implementation::bindType(const string& name,
                                           const vector<Type>& params, Type t,
                                           bool levelZero) throw() {
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

bool SymbolTable::Implementation::isBoundType(const string& name) const
    throw() {
  return d_typeMap->find(name) != d_typeMap->end();
}

Type SymbolTable::Implementation::lookupType(const string& name) const throw() {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == 0, name,
                      "type constructor arity is wrong: "
                      "`%s' requires %u parameters but was provided 0",
                      name.c_str(), p.first.size());
  return p.second;
}

Type SymbolTable::Implementation::lookupType(const string& name,
                                             const vector<Type>& params) const
    throw() {
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

void SymbolTable::Implementation::popScope() throw(ScopeException) {
  if (d_context.getLevel() == 0) {
    throw ScopeException();
  }
  d_context.pop();
}

void SymbolTable::Implementation::pushScope() throw() { d_context.push(); }

size_t SymbolTable::Implementation::getLevel() const throw() {
  return d_context.getLevel();
}

void SymbolTable::Implementation::reset() {
  this->SymbolTable::Implementation::~Implementation();
  new (this) SymbolTable::Implementation();
}

bool SymbolTable::Implementation::isOverloadedFunction(Expr fun) const {
  return d_overload_trie->isOverloadedFunction(fun);
}

Expr SymbolTable::Implementation::getOverloadedConstantForType(const std::string& name, Type t) const {
  return d_overload_trie->getOverloadedConstantForType(name, t);
}

Expr SymbolTable::Implementation::getOverloadedFunctionForTypes(const std::string& name, 
                                                                const std::vector< Type >& argTypes) const {
  return d_overload_trie->getOverloadedFunctionForTypes(name, argTypes);
}

void SymbolTable::Implementation::bindWithOverloading(const string& name, Expr obj){
  CDHashMap<string, Expr>::const_iterator it = d_exprMap->find(name);
  if(it != d_exprMap->end()) {
    const Expr& prev_bound_obj = (*it).second;
    if(prev_bound_obj!=obj) {
      d_overload_trie->bind(name, prev_bound_obj, obj);
    }
  }
}

bool SymbolTable::isOverloadedFunction(Expr fun) const {
  return d_implementation->isOverloadedFunction(fun);
}

Expr SymbolTable::getOverloadedConstantForType(const std::string& name, Type t) const {
  return d_implementation->getOverloadedConstantForType(name, t);
}

Expr SymbolTable::getOverloadedFunctionForTypes(const std::string& name, 
                                                const std::vector< Type >& argTypes) const {
  return d_implementation->getOverloadedFunctionForTypes(name, argTypes);
}

SymbolTable::SymbolTable()
    : d_implementation(new SymbolTable::Implementation()) {}

SymbolTable::~SymbolTable() {}

void SymbolTable::bind(const string& name, Expr obj, bool levelZero, bool doOverload) throw() {
  d_implementation->bind(name, obj, levelZero, doOverload);
}

void SymbolTable::bindDefinedFunction(const string& name, Expr obj,
                                      bool levelZero, bool doOverload) throw() {
  d_implementation->bindDefinedFunction(name, obj, levelZero, doOverload);
}

void SymbolTable::bindType(const string& name, Type t, bool levelZero) throw() {
  d_implementation->bindType(name, t, levelZero);
}

void SymbolTable::bindType(const string& name, const vector<Type>& params,
                           Type t, bool levelZero) throw() {
  d_implementation->bindType(name, params, t, levelZero);
}

bool SymbolTable::isBound(const string& name) const throw() {
  return d_implementation->isBound(name);
}

bool SymbolTable::isBoundDefinedFunction(const string& name) const throw() {
  return d_implementation->isBoundDefinedFunction(name);
}

bool SymbolTable::isBoundDefinedFunction(Expr func) const throw() {
  return d_implementation->isBoundDefinedFunction(func);
}
bool SymbolTable::isBoundType(const string& name) const throw() {
  return d_implementation->isBoundType(name);
}
Expr SymbolTable::lookup(const string& name) const throw() {
  return d_implementation->lookup(name);
}
Type SymbolTable::lookupType(const string& name) const throw() {
  return d_implementation->lookupType(name);
}

Type SymbolTable::lookupType(const string& name,
                             const vector<Type>& params) const throw() {
  return d_implementation->lookupType(name, params);
}
size_t SymbolTable::lookupArity(const string& name) {
  return d_implementation->lookupArity(name);
}
void SymbolTable::popScope() throw(ScopeException) {
  d_implementation->popScope();
}

void SymbolTable::pushScope() throw() { d_implementation->pushScope(); }
size_t SymbolTable::getLevel() const throw() {
  return d_implementation->getLevel();
}
void SymbolTable::reset() { d_implementation->reset(); }

}  // namespace CVC4

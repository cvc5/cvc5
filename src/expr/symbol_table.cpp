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

class SymbolTable::Implementation {
 public:
  Implementation()
      : d_context(),
        d_exprMap(new (true) CDHashMap<string, Expr>(&d_context)),
        d_typeMap(new (true) TypeMap(&d_context)),
        d_functions(new (true) CDHashSet<Expr, ExprHashFunction>(&d_context)) {}

  ~Implementation() {
    d_exprMap->deleteSelf();
    d_typeMap->deleteSelf();
    d_functions->deleteSelf();
  }

  void bind(const string& name, Expr obj, bool levelZero) throw();
  void bindDefinedFunction(const string& name, Expr obj,
                           bool levelZero) throw();
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
}; /* SymbolTable::Implementation */

void SymbolTable::Implementation::bind(const string& name, Expr obj,
                                       bool levelZero) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  if (levelZero) {
    d_exprMap->insertAtContextLevelZero(name, obj);
  } else {
    d_exprMap->insert(name, obj);
  }
}

void SymbolTable::Implementation::bindDefinedFunction(const string& name,
                                                      Expr obj,
                                                      bool levelZero) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
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
  return (*d_exprMap->find(name)).second;
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

SymbolTable::SymbolTable()
    : d_implementation(new SymbolTable::Implementation()) {}

SymbolTable::~SymbolTable() {}

void SymbolTable::bind(const string& name, Expr obj, bool levelZero) throw() {
  d_implementation->bind(name, obj, levelZero);
}

void SymbolTable::bindDefinedFunction(const string& name, Expr obj,
                                      bool levelZero) throw() {
  d_implementation->bindDefinedFunction(name, obj, levelZero);
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

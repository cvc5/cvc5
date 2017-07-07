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

#include <string>
#include <utility>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/context.h"
#include "expr/expr.h"
#include "expr/expr_manager_scope.h"
#include "expr/type.h"


using namespace CVC4::context;
using namespace std;

namespace CVC4 {

SymbolTable::SymbolTable() :
  d_context(new Context()),
  d_exprMap(new(true) CDHashMap<std::string, Expr, StringHashFunction>(d_context)),
  d_typeMap(new(true) CDHashMap<std::string, pair<vector<Type>, Type>, StringHashFunction>(d_context)),
  d_functions(new(true) CDHashSet<Expr, ExprHashFunction>(d_context)) {
}

SymbolTable::~SymbolTable() {
  d_exprMap->deleteSelf();
  d_typeMap->deleteSelf();
  d_functions->deleteSelf();
  delete d_context;
}

void SymbolTable::bind(const std::string& name, Expr obj,
                       bool levelZero) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  if(levelZero) d_exprMap->insertAtContextLevelZero(name, obj);
  else d_exprMap->insert(name, obj);
}

void SymbolTable::bindDefinedFunction(const std::string& name, Expr obj,
                                      bool levelZero) throw() {
  PrettyCheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  if(levelZero){
    d_exprMap->insertAtContextLevelZero(name, obj);
    d_functions->insertAtContextLevelZero(obj);
  } else {
    d_exprMap->insert(name, obj);
    d_functions->insert(obj);
  }
}

bool SymbolTable::isBound(const std::string& name) const throw() {
  return d_exprMap->find(name) != d_exprMap->end();
}

bool SymbolTable::isBoundDefinedFunction(const std::string& name) const throw() {
  CDHashMap<std::string, Expr, StringHashFunction>::iterator found =
    d_exprMap->find(name);
  return found != d_exprMap->end() && d_functions->contains((*found).second);
}

bool SymbolTable::isBoundDefinedFunction(Expr func) const throw() {
  return d_functions->contains(func);
}

Expr SymbolTable::lookup(const std::string& name) const throw() {
  return (*d_exprMap->find(name)).second;
}

void SymbolTable::bindType(const std::string& name, Type t,
                           bool levelZero) throw() {
  if(levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(vector<Type>(), t));
  } else {
    d_typeMap->insert(name, make_pair(vector<Type>(), t));
  }
}

void SymbolTable::bindType(const std::string& name,
                           const std::vector<Type>& params,
                           Type t,
                           bool levelZero) throw() {
  if(Debug.isOn("sort")) {
    Debug("sort") << "bindType(" << name << ", [";
    if(params.size() > 0) {
      copy( params.begin(), params.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << params.back();
    }
    Debug("sort") << "], " << t << ")" << endl;
  }
  if(levelZero) {
    d_typeMap->insertAtContextLevelZero(name, make_pair(params, t));
  } else {
    d_typeMap->insert(name, make_pair(params, t));
  }
}

bool SymbolTable::isBoundType(const std::string& name) const throw() {
  return d_typeMap->find(name) != d_typeMap->end();
}

Type SymbolTable::lookupType(const std::string& name) const throw() {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == 0, name,
                "type constructor arity is wrong: "
                "`%s' requires %u parameters but was provided 0",
                name.c_str(), p.first.size());
  return p.second;
}

Type SymbolTable::lookupType(const std::string& name,
                             const std::vector<Type>& params) const throw() {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  PrettyCheckArgument(p.first.size() == params.size(), params,
                "type constructor arity is wrong: "
                "`%s' requires %u parameters but was provided %u",
         name.c_str(), p.first.size(), params.size());
  if(p.first.size() == 0) {
    PrettyCheckArgument(p.second.isSort(), name.c_str());
    return p.second;
  }
  if(p.second.isSortConstructor()) {
    if(Debug.isOn("sort")) {
      Debug("sort") << "instantiating using a sort constructor" << endl;
      Debug("sort") << "have formals [";
      copy( p.first.begin(), p.first.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << p.first.back() << "]" << endl
                    << "parameters   [";
      copy( params.begin(), params.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Type instantiation =
      SortConstructorType(p.second).instantiate(params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  } else if(p.second.isDatatype()) {
    PrettyCheckArgument(DatatypeType(p.second).isParametric(), name, "expected parametric datatype");
    return DatatypeType(p.second).instantiate(params);
  } else {
    if(Debug.isOn("sort")) {
      Debug("sort") << "instantiating using a sort substitution" << endl;
      Debug("sort") << "have formals [";
      copy( p.first.begin(), p.first.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << p.first.back() << "]" << endl
                    << "parameters   [";
      copy( params.begin(), params.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << params.back() << "]" << endl
                    << "type ctor    " << name << endl
                    << "type is      " << p.second << endl;
    }

    Type instantiation = p.second.substitute(p.first, params);

    Debug("sort") << "instance is  " << instantiation << endl;

    return instantiation;
  }
}

size_t SymbolTable::lookupArity(const std::string& name) {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  return p.first.size();
}

void SymbolTable::popScope() throw(ScopeException) {
  if( d_context->getLevel() == 0 ) {
    throw ScopeException();
  }
  d_context->pop();
}

void SymbolTable::pushScope() throw() {
  d_context->push();
}

size_t SymbolTable::getLevel() const throw() {
  return d_context->getLevel();
}

void SymbolTable::reset() {
  this->SymbolTable::~SymbolTable();
  new(this) SymbolTable();
}

}/* CVC4 namespace */

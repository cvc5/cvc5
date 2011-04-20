/*********************                                                        */
/*! \file declaration_scope.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type
 ** declarations (implementation).
 **
 ** Convenience class for scoping variable and type declarations
 ** (implementation).
 **/

#include "expr/declaration_scope.h"
#include "expr/expr.h"
#include "expr/type.h"
#include "expr/expr_manager_scope.h"
#include "context/cdmap.h"
#include "context/cdset.h"
#include "context/context.h"

#include <string>
#include <utility>

using namespace CVC4;
using namespace CVC4::context;
using namespace std;

namespace CVC4 {

DeclarationScope::DeclarationScope() :
  d_context(new Context),
  d_exprMap(new(true) CDMap<std::string, Expr, StringHashFunction>(d_context)),
  d_typeMap(new(true) CDMap<std::string, pair<vector<Type>, Type>, StringHashFunction>(d_context)),
  d_functions(new(true) CDSet<Expr, ExprHashFunction>(d_context)) {
}

DeclarationScope::~DeclarationScope() {
  d_exprMap->deleteSelf();
  d_typeMap->deleteSelf();
  d_functions->deleteSelf();
  delete d_context;
}

void DeclarationScope::bind(const std::string& name, Expr obj) throw(AssertionException) {
  CheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  d_exprMap->insert(name, obj);
}

void DeclarationScope::bindDefinedFunction(const std::string& name, Expr obj) throw(AssertionException) {
  CheckArgument(!obj.isNull(), obj, "cannot bind to a null Expr");
  ExprManagerScope ems(obj);
  d_exprMap->insert(name, obj);
  d_functions->insert(obj);
}

bool DeclarationScope::isBound(const std::string& name) const throw() {
  return d_exprMap->find(name) != d_exprMap->end();
}

bool DeclarationScope::isBoundDefinedFunction(const std::string& name) const throw() {
  CDMap<std::string, Expr, StringHashFunction>::iterator found =
    d_exprMap->find(name);
  return found != d_exprMap->end() && d_functions->contains((*found).second);
}

bool DeclarationScope::isBoundDefinedFunction(Expr func) const throw() {
  return d_functions->contains(func);
}

Expr DeclarationScope::lookup(const std::string& name) const throw(AssertionException) {
  return (*d_exprMap->find(name)).second;
}

void DeclarationScope::bindType(const std::string& name, Type t) throw() {
  d_typeMap->insert(name, make_pair(vector<Type>(), t));
}

void DeclarationScope::bindType(const std::string& name,
                                const std::vector<Type>& params,
                                Type t) throw() {
  if(Debug.isOn("sort")) {
    Debug("sort") << "bindType(" << name << ", [";
    if(params.size() > 0) {
      copy( params.begin(), params.end() - 1,
            ostream_iterator<Type>(Debug("sort"), ", ") );
      Debug("sort") << params.back();
    }
    Debug("sort") << "], " << t << ")" << endl;
  }
  d_typeMap->insert(name, make_pair(params, t));
}

bool DeclarationScope::isBoundType(const std::string& name) const throw() {
  return d_typeMap->find(name) != d_typeMap->end();
}

Type DeclarationScope::lookupType(const std::string& name) const throw(AssertionException) {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  Assert(p.first.size() == 0,
         "type constructor arity is wrong: "
         "`%s' requires %u parameters but was provided 0",
         name.c_str(), p.first.size());
  return p.second;
}

Type DeclarationScope::lookupType(const std::string& name,
                                  const std::vector<Type>& params) const throw(AssertionException) {
  pair<vector<Type>, Type> p = (*d_typeMap->find(name)).second;
  Assert(p.first.size() == params.size(),
         "type constructor arity is wrong: "
         "`%s' requires %u parameters but was provided %u",
         name.c_str(), p.first.size(), params.size());
  if(p.first.size() == 0) {
    Assert(p.second.isSort());
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

void DeclarationScope::popScope() throw(ScopeException) {
  if( d_context->getLevel() == 0 ) {
    throw ScopeException();
  }
  d_context->pop();
}

void DeclarationScope::pushScope() throw() {
  d_context->push();
}

size_t DeclarationScope::getLevel() const throw() {
  return d_context->getLevel();
}

}/* CVC4 namespace */

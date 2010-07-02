/*********************                                                        */
/*! \file declaration_scope.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Convenience class for scoping variable and type declarations (implementation).
 **
 ** Convenience class for scoping variable and type declarations (implementation)
 **/

#include "declaration_scope.h"
#include "expr.h"
#include "type.h"

#include "context/cdmap.h"
#include "context/context.h"

#include <string>

namespace CVC4 {

using namespace context;

DeclarationScope::DeclarationScope() :
  d_context(new Context()),
  d_exprMap(new (true) CDMap<std::string,Expr,StringHashFunction>(d_context)),
  d_typeMap(new (true) CDMap<std::string,Type,StringHashFunction>(d_context)) {
}

DeclarationScope::~DeclarationScope() {
  d_exprMap->deleteSelf();
  d_typeMap->deleteSelf();
  delete d_context;
}

void DeclarationScope::bind(const std::string& name, const Expr& obj) throw () {
  d_exprMap->insert(name,obj);
}

bool DeclarationScope::isBound(const std::string& name) const throw () {
  return d_exprMap->find(name) != d_exprMap->end();
}

Expr DeclarationScope::lookup(const std::string& name) const throw () {
  return (*d_exprMap->find(name)).second;
}

void DeclarationScope::bindType(const std::string& name, const Type& t) throw () {
  d_typeMap->insert(name,t);
}

bool DeclarationScope::isBoundType(const std::string& name) const throw () {
  return d_typeMap->find(name) != d_typeMap->end();
}

Type DeclarationScope::lookupType(const std::string& name) const throw () {
  return (*d_typeMap->find(name)).second;
}


void DeclarationScope::popScope() throw (ScopeException) {
  if( d_context->getLevel() == 0 ) {
    throw ScopeException();
  }
  d_context->pop();
}

void DeclarationScope::pushScope() throw () {
  d_context->push();
}

} // namespace CVC4

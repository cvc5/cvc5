/*********************                                           -*- C++ -*-  */
/** type.h
 ** Original author: cconway
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Implementation of expression types 
 **/

#include "expr/expr_manager.h"
#include "expr/type.h"
#include "util/Assert.h"
#include <string>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Type& e) {
  e.toStream(out);
  return out;
}

Type::Type(ExprManager* exprManager) : 
  d_exprManager(exprManager), d_name(std::string("<undefined>")) { 
}

Type::Type(ExprManager* exprManager, std::string name) : 
  d_exprManager(exprManager), d_name(name) { 
}

// Type Type::operator=(const Type& t) {
//   if( this != &t ) {
//     d_name == t.d_name;
// }

bool Type::operator==(const Type& t) const {
  return d_name == t.d_name;
}

bool Type::operator!=(const Type& t) const {
  return !(*this == t);
}

ExprManager* Type::getExprManager() const {
  return d_exprManager;
}

std::string Type::getName() const {
  return d_name;
}

// void Type::toStream(std::ostream& out) const {
//   out << getName();
// }

BooleanType::BooleanType(ExprManager* exprManager) 
  : Type(exprManager,std::string("BOOLEAN")) {
}

BooleanType::~BooleanType() {
}

bool BooleanType::isBoolean() const {
  return true;
}

FunctionType::FunctionType(ExprManager* exprManager, 
                           const Type* domain, 
                           const Type* range) 
  : Type(exprManager), d_argTypes(), d_rangeType(range) {
  d_argTypes.push_back(domain);
}

  // FIXME: What becomes of argument types?
FunctionType::~FunctionType() {
}

FunctionType::FunctionType(ExprManager* exprManager, 
                           const std::vector<const Type*>& argTypes, 
                           const Type* range) 
  : Type(exprManager), d_argTypes(argTypes), d_rangeType(range) {
  Assert( argTypes.size() > 0 );
}

const std::vector<const Type*> FunctionType::getArgTypes() const {
  return d_argTypes;
}

const Type* FunctionType::getRangeType() const {
  return d_rangeType;
}

bool FunctionType::isFunction() const {
  return true;
}

bool FunctionType::isPredicate() const {
  return d_rangeType == d_exprManager->booleanType();
}

void FunctionType::toStream(std::ostream& out) const {
  if( d_argTypes.size() > 1 ) {
    out << "(";
  }
  for( unsigned int i=0; i < d_argTypes.size(); ++i ) {
    if( i > 0 ) {
      out << ",";
    }
    d_argTypes[i]->toStream(out);
  }
  if( d_argTypes.size() > 1 ) {
    out << ")";
  }
  out << " -> ";
  d_rangeType->toStream(out);
}

KindType::KindType(ExprManager* exprManager) 
  : Type(exprManager,std::string("KIND")) {
}

KindType::~KindType() {
}

bool KindType::isKind() const {
  return true;
}

SortType::SortType(ExprManager* exprManager,std::string name) 
  : Type(exprManager,name) {
}

SortType::~SortType() {
}


}

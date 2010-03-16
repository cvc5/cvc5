/*********************                                                        */
/** type.cpp
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

#include "expr/node_manager.h"
#include "expr/type.h"
#include "util/Assert.h"
#include <string>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Type& e) {
  e.toStream(out);
  return out;
}

Type::Type() :
  d_name(std::string("<undefined>")),
  d_rc(0) {
}

Type::Type(std::string name) : 
  d_name(name) {
}

std::string Type::getName() const {
  return d_name;
}

BooleanType BooleanType::s_instance;

BooleanType::BooleanType() :
  Type(std::string("BOOLEAN")) {
  d_rc = RC_MAX;// singleton, not heap-allocated
}

BooleanType::~BooleanType() {
}

BooleanType*
BooleanType::getInstance() {
  return &s_instance;
}

bool BooleanType::isBoolean() const {
  return true;
}

FunctionType::FunctionType(const std::vector<Type*>& argTypes,
                           Type* range) :
  d_argTypes(argTypes),
  d_rangeType(range) {

  Assert( argTypes.size() > 0 );
}

// FIXME: What becomes of argument types?
FunctionType::~FunctionType() {
}

const std::vector<Type*> FunctionType::getArgTypes() const {
  return d_argTypes;
}

Type* FunctionType::getRangeType() const {
  return d_rangeType;
}

bool FunctionType::isFunction() const {
  return true;
}

bool FunctionType::isPredicate() const {
  return d_rangeType->isBoolean();
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

KindType KindType::s_instance;

KindType::KindType() :
  Type(std::string("KIND")) {
  d_rc = RC_MAX;// singleton, not heap-allocated
}

KindType::~KindType() {
}

bool KindType::isKind() const {
  return true;
}

KindType*
KindType::getInstance() {
  return &s_instance;
}

SortType::SortType(std::string name) :
  Type(name) {
}

SortType::~SortType() {
}

}

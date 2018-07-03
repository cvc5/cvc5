/*********************                                                        */
/*! \file cvc4cpp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The CVC4 C++ API.
 **
 ** The CVC4 C++ API.
 **/

#include "api/cvc4cpp.h"

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/type.h"
#include "util/result.h"

#include <sstream>

namespace CVC4 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Result                                                                     */
/* -------------------------------------------------------------------------- */

Result::Result(const CVC4::Result& r) : d_result(new CVC4::Result(r)) {}

bool Result::isSat(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::SAT;
}

bool Result::isUnsat(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::UNSAT;
}

bool Result::isSatUnknown(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_SAT
         && d_result->isSat() == CVC4::Result::SAT_UNKNOWN;
}

bool Result::isValid(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::VALID;
}

bool Result::isInvalid(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::INVALID;
}

bool Result::isValidUnknown(void) const
{
  return d_result->getType() == CVC4::Result::TYPE_VALIDITY
         && d_result->isValid() == CVC4::Result::VALIDITY_UNKNOWN;
}

bool Result::operator==(const Result& r) const
{
  return *d_result == *r.d_result;
}

bool Result::operator!=(const Result& r) const
{
  return *d_result != *r.d_result;
}

std::string Result::getUnknownExplanation(void) const
{
  std::stringstream ss;
  ss << d_result->whyUnknown();
  return ss.str();
}

std::string Result::toString(void) const { return d_result->toString(); }

std::ostream& operator<<(std::ostream& out, const Result& r)
{
  out << r.toString();
  return out;
}

/* -------------------------------------------------------------------------- */
/* Sort                                                                       */
/* -------------------------------------------------------------------------- */

Sort::Sort(const CVC4::Type& t) : d_type(new CVC4::Type(t))
{
}

Sort::~Sort()
{
}

Sort& Sort::operator=(const Sort& s)
{
  // CHECK: valid sort s?
  if (this != &s)
  {
    *d_type = *s.d_type;
  }
  return *this;
}

bool Sort::operator==(const Sort& s) const
{
  // CHECK: valid sort s?
  return *d_type == *s.d_type;
}

bool Sort::operator!=(const Sort& s) const
{
  // CHECK: valid sort s?
  return *d_type != *s.d_type;
}

bool Sort::isBoolean() const
{
  // CHECK: valid sort s?
  return d_type->isBoolean();
}

bool Sort::isInteger() const
{
  // CHECK: valid sort s?
  return d_type->isInteger();
}

bool Sort::isReal() const
{
  // CHECK: valid sort s?
  return d_type->isReal();
}

bool Sort::isString() const
{
  // CHECK: valid sort s?
  return d_type->isString();
}

bool Sort::isRegExp() const
{
  // CHECK: valid sort s?
  return d_type->isRegExp();
}

bool Sort::isRoundingMode() const
{
  // CHECK: valid sort s?
  return d_type->isRoundingMode();
}

bool Sort::isBitVector() const
{
  // CHECK: valid sort s?
  return d_type->isBitVector();
}

bool Sort::isFloatingPoint() const
{
  // CHECK: valid sort s?
  return d_type->isFloatingPoint();
}

bool Sort::isDatatype() const
{
  // CHECK: valid sort s?
  return d_type->isDatatype();
}

bool Sort::isFunction() const
{
  // CHECK: valid sort s?
  return d_type->isFunction();
}

bool Sort::isPredicate() const
{
  // CHECK: valid sort s?
  return d_type->isPredicate();
}

bool Sort::isTuple() const
{
  // CHECK: valid sort s?
  return d_type->isTuple();
}

bool Sort::isRecord() const
{
  // CHECK: valid sort s?
  return d_type->isRecord();
}

bool Sort::isArray() const
{
  // CHECK: valid sort s?
  return d_type->isArray();
}

bool Sort::isSet() const
{
  // CHECK: valid sort s?
  return d_type->isSet();
}

bool Sort::isUninterpretedSort() const
{
  // CHECK: valid sort s?
  return d_type->isSort();
}

bool Sort::isSortConstructor() const
{
  // CHECK: valid sort s?
  return d_type->isSortConstructor();
}

#if 0
Datatype Sort::getDatatype() const
{
  // CHECK: is this a datatype sort?
  DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
  return type->getDatatype();
}

Sort Sort::instantiate(const std::vector<Sort>& params) const
{
  // CHECK: Is this a datatype/sort constructor sort?
  std::vector<Type> tparams;
  for (const Sort& s : params) { tparams.push_back(*s.d_type.get()); }
  if (d_type->isDatatype())
  {
    // CHECK: is parametric?
    DatatypeType* type = static_cast<DatatypeType*>(d_type.get());
    return type->instantiate(tparams);
  }
  Assert (d_type->isSortConstructor());
  return static_cast<SortConstructorType*>(d_type.get())->instantiate(tparams);
}
#endif

std::string Sort::toString() const
{
  // CHECK: valid sort s?
  return d_type->toString();
}

std::ostream& operator<< (std::ostream& out, const Sort& s)
{
  out << s.toString();
  return out;
}

size_t SortHashFunction::operator()(const Sort& s) const {
  return TypeHashFunction()(*s.d_type);
}


/* -------------------------------------------------------------------------- */
/* Datatypes                                                                  */
/* -------------------------------------------------------------------------- */

/* DatatypeSelectorDecl ----------------------------------------------------- */

DatatypeSelectorDecl::DatatypeSelectorDecl(const std::string& name, Sort sort)
    : d_name(name), d_sort(sort)
{
}

DatatypeSelectorDecl::DatatypeSelectorDecl(const std::string& name,
                                           DatatypeDeclSelfSort sort)
    : d_name(name), d_sort(Sort(CVC4::Type()))
{
}

std::string DatatypeSelectorDecl::toString() const
{
  std::stringstream ss;
  ss << d_name << ": " << d_sort;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, const DatatypeDecl& dtdecl)
{
  out << dtdecl.toString();
  return out;
}

/* DatatypeConstructorDecl -------------------------------------------------- */

DatatypeConstructorDecl::DatatypeConstructorDecl(const std::string& name)
    : d_ctor(new CVC4::DatatypeConstructor(name))
{
}

void DatatypeConstructorDecl::addSelector(const DatatypeSelectorDecl& stor)
{
  CVC4::Type t = *stor.d_sort.d_type;
  if (t.isNull())
  {
    d_ctor->addArg(stor.d_name, DatatypeSelfType());
  }
  else
  {
    d_ctor->addArg(stor.d_name, t);
  }
}

std::string DatatypeConstructorDecl::toString() const
{
  std::stringstream ss;
  ss << *d_ctor;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out,
                         const DatatypeConstructorDecl& ctordecl)
{
  out << ctordecl.toString();
  return out;
}

/* DatatypeDecl ------------------------------------------------------------- */

DatatypeDecl::DatatypeDecl(const std::string& name, bool isCoDatatype)
    : d_dtype(new CVC4::Datatype(name, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const std::string& name,
                           Sort param,
                           bool isCoDatatype)
    : d_dtype(new CVC4::Datatype(
          name, std::vector<Type>{*param.d_type}, isCoDatatype))
{
}

DatatypeDecl::DatatypeDecl(const std::string& name,
                           const std::vector<Sort>& params,
                           bool isCoDatatype)
{
  std::vector<Type> tparams;
  for (const Sort& s : params) { tparams.push_back(*s.d_type); }
  d_dtype = std::shared_ptr<CVC4::Datatype>(
      new CVC4::Datatype(name, tparams, isCoDatatype));
}

DatatypeDecl::~DatatypeDecl()
{
}

void DatatypeDecl::addConstructor(const DatatypeConstructorDecl& ctor)
{
  d_dtype->addConstructor(*ctor.d_ctor);
}

std::string DatatypeDecl::toString() const
{
  std::stringstream ss;
  ss << *d_dtype;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out,
                         const DatatypeSelectorDecl& stordecl)
{
  out << stordecl.toString();
  return out;
}

}  // namespace api
}  // namespace CVC4

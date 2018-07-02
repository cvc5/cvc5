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

#include "base/cvc4_assert.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/type.h"
#include "util/result.h"
#include "util/utility.h"

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
/* Term                                                                       */
/* -------------------------------------------------------------------------- */

Term::Term() : d_expr(new CVC4::Expr())
{
}

Term::Term(const CVC4::Expr& e) : d_expr(new CVC4::Expr(e))
{
}

Term::~Term()
{
}

Term& Term::operator=(const Term& t)
{
  // CHECK: expr managers must match
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool Term::operator==(const Term& t) const
{
  // CHECK: expr managers must match
  return *d_expr == *t.d_expr;
}

bool Term::operator!=(const Term& t) const
{
  // CHECK: expr managers must match
  return *d_expr != *t.d_expr;
}

#if 0
Kind Term::getKind() const
{
  return s_kinds_internal[d_expr->getKind()];
}

Sort Term::getSort() const
{
  return Sort(d_expr->getType());
}
#endif

bool Term::isNull() const
{
  return d_expr->isNull();
}

Term Term::notTerm() const
{
  return d_expr->notExpr();
}

Term Term::andTerm(const Term& t) const
{
  return d_expr->andExpr(*t.d_expr);
}

Term Term::orTerm(const Term& t) const
{
  return d_expr->orExpr(*t.d_expr);
}

Term Term::xorTerm(const Term& t) const
{
  return d_expr->xorExpr(*t.d_expr);
}

Term Term::iffTerm(const Term& t) const
{
  return d_expr->iffExpr(*t.d_expr);
}

Term Term::impTerm(const Term& t) const
{
  return d_expr->impExpr(*t.d_expr);
}

Term Term::iteTerm(const Term& then_t, const Term& else_t) const
{
  return d_expr->iteExpr(*then_t.d_expr, *else_t.d_expr);
}

std::string Term::toString() const
{
  return d_expr->toString();
}

Term::const_iterator::const_iterator() : d_iterator(nullptr)
{
}

Term::const_iterator::const_iterator(void* it) : d_iterator(it)
{
}

Term::const_iterator::const_iterator(const const_iterator& it)
    : d_iterator(nullptr)
{
  if (it.d_iterator != nullptr)
  {
    d_iterator = new CVC4::Expr::const_iterator(
        *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator));
  }
}

Term::const_iterator& Term::const_iterator::operator=(const const_iterator& it)
{
  if (d_iterator != nullptr)
  {
    delete static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  }
  d_iterator = new CVC4::Expr::const_iterator(
      *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator));
  return *this;
}

Term::const_iterator::~const_iterator()
{
  if (d_iterator != nullptr)
  {
    delete static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  }
}

bool Term::const_iterator::operator==(const const_iterator& it) const
{
  if (d_iterator == nullptr || it.d_iterator == nullptr)
  {
    return false;
  }
  return *static_cast<CVC4::Expr::const_iterator*>(d_iterator)
         == *static_cast<CVC4::Expr::const_iterator*>(it.d_iterator);
}

bool Term::const_iterator::operator!=(const const_iterator& it) const
{
  return !(*this == it);
}

Term::const_iterator& Term::const_iterator::operator++()
{
  Assert(d_iterator != nullptr);
  ++*static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  return *this;
}

Term::const_iterator Term::const_iterator::operator++(int)
{
  Assert(d_iterator != nullptr);
  const_iterator it = *this;
  ++*static_cast<CVC4::Expr::const_iterator*>(d_iterator);
  return it;
}

Term Term::const_iterator::operator*() const
{
  Assert(d_iterator != nullptr);
  return Term(**static_cast<CVC4::Expr::const_iterator*>(d_iterator));
}

Term::const_iterator Term::begin() const
{
  return Term::const_iterator(new CVC4::Expr::const_iterator(d_expr->begin()));
}

Term::const_iterator Term::end() const
{
  return Term::const_iterator(new CVC4::Expr::const_iterator(d_expr->end()));
}

std::ostream& operator<< (std::ostream& out, const Term& t)
{
  out << t.toString();
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::vector<Term>& vector)
{
  container_to_stream(out, vector);
  return out;
}

std::ostream& operator<<(std::ostream& out, const std::set<Term>& set)
{
  container_to_stream(out, set);
  return out;
}

std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_set<Term, TermHashFunction>& unordered_set)
{
  container_to_stream(out, unordered_set);
  return out;
}

template <typename V>
std::ostream& operator<<(std::ostream& out, const std::map<Term, V>& map)
{
  container_to_stream(out, map);
  return out;
}

template <typename V>
std::ostream& operator<<(
    std::ostream& out,
    const std::unordered_map<Term, V, TermHashFunction>& unordered_map)
{
  container_to_stream(out, unordered_map);
  return out;
}

size_t TermHashFunction::operator()(const Term& t) const
{
  return ExprHashFunction()(*t.d_expr);
}
}  // namespace api
}  // namespace CVC4

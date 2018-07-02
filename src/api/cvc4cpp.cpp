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
/* OpTerm                                                                     */
/* -------------------------------------------------------------------------- */

OpTerm::OpTerm() : d_expr(new CVC4::Expr())
{
}

OpTerm::OpTerm(const CVC4::Expr& e) : d_expr(new CVC4::Expr(e))
{
}

OpTerm::~OpTerm()
{
}

OpTerm& OpTerm::operator=(const OpTerm& t)
{
  // CHECK: expr managers must match
  if (this != &t)
  {
    *d_expr = *t.d_expr;
  }
  return *this;
}

bool OpTerm::operator==(const OpTerm& t) const
{
  // CHECK: expr managers must match
  return *d_expr == *t.d_expr;
}

bool OpTerm::operator!=(const OpTerm& t) const
{
  // CHECK: expr managers must match
  return *d_expr != *t.d_expr;
}

#if 0
Kind OpTerm::getKind() const
{
  return s_kinds_internal[d_expr->getKind()];
}

Sort OpTerm::getSort() const
{
  return Sort(d_expr->getType());
}
#endif

bool OpTerm::isNull() const
{
  return d_expr->isNull();
}

std::string OpTerm::toString() const
{
  return d_expr->toString();
}

std::ostream& operator<< (std::ostream& out, const OpTerm& t)
{
  out << t.toString();
  return out;
}

size_t OpTermHashFunction::operator()(const OpTerm& t) const
{
  return ExprHashFunction()(*t.d_expr);
}

}  // namespace api
}  // namespace CVC4

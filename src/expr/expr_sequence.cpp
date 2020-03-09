/*********************                                                        */
/*! \file sequence.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the sequence data type.
 **/

#include "expr/expr_sequence.h"

#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

ExprSequence::ExprSequence(const Type& t)
{
  d_type.reset(new Type(t));
}
ExprSequence::~ExprSequence() {}

ExprSequence::ExprSequence(const ExprSequence& other)
    : d_type(new ArrayType(other.getType())),
      d_expr(new Expr(other.getExpr())) {}

ExprSequence& ExprSequence::operator=(const ExprSequence& other) {
  (*d_type) = other.getType();
  (*d_expr) = other.getExpr();
  return *this;
}

const Type& ExprSequence::getType() const { return *d_type; }

const Expr& getExpr() const {
  return *d_expr;
}

size_t ExprSequenceHashFunction::operator()(const ExprSequence& es) const {
  return TypeHashFunction()(es.getType());
}

bool ExprSequence::operator==(const ExprSequence& es) const
{
  return getType() == es.getType() && getExpr() == es.getExpr();
}

bool ExprSequence::operator!=(const ExprSequence& es) const
{
  return !(*this == es);
}

bool ExprSequence::operator<(const ExprSequence& es) const
{
  return (getType() < es.getType()) ||
         (getType() == es.getType() && getExpr() < es.getExpr());
}

bool ExprSequence::operator<=(const ExprSequence& es) const
{
  return (getType() < es.getType()) ||
         (getType() == es.getType() && getExpr() <= es.getExpr());
}

bool ExprSequence::operator>(const ExprSequence& es) const
{
  return !(*this <= es);
}

bool ExprSequence::operator>=(const ExprSequence& es) const
{
  return !(*this < es);
}

std::ostream& operator<<(std::ostream& os, const Sequence& s)
{
  // FIXME
  return os << "\""
            << "\"";
}

}  // namespace CVC4

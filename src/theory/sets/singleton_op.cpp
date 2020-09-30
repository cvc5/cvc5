/*********************                                                        */
/*! \file singleton_op.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief a class for singleton operator for sets
 **/

#include "singleton_op.h"

#include <iostream>

#include "expr/type_node.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const SingletonOp& asa)
{
  return out << "(singleton_op " << asa.getType() << ')';
}

size_t SingletonOpHashFunction::operator()(const SingletonOp& es) const
{
  return TypeNodeHashFunction()(es.getType());
}

/**
 * Constructs an singleton of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
SingletonOp::SingletonOp(const TypeNode& setType)
    : d_type(new TypeNode(setType))
{
}

SingletonOp::SingletonOp(const SingletonOp& es)
    : d_type(new TypeNode(es.getType()))
{
}

SingletonOp& SingletonOp::operator=(const SingletonOp& es)
{
  (*d_type) = es.getType();
  return *this;
}

SingletonOp::~SingletonOp() {}
const TypeNode& SingletonOp::getType() const { return *d_type; }
bool SingletonOp::operator==(const SingletonOp& es) const
{
  return getType() == es.getType();
}

bool SingletonOp::operator!=(const SingletonOp& es) const
{
  return !(*this == es);
}
bool SingletonOp::operator<(const SingletonOp& es) const
{
  return getType() < es.getType();
}

bool SingletonOp::operator<=(const SingletonOp& es) const
{
  return getType() <= es.getType();
}

bool SingletonOp::operator>(const SingletonOp& es) const
{
  return !(*this <= es);
}
bool SingletonOp::operator>=(const SingletonOp& es) const
{
  return !(*this < es);
}
}  // namespace CVC4

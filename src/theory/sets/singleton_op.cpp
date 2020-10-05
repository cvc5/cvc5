/*********************                                                        */
/*! \file singleton_op.cpp
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

std::ostream& operator<<(std::ostream& out, const SingletonOp& op)
{
  return out << "(singleton_op " << op.getType() << ')';
}

size_t SingletonOpHashFunction::operator()(const SingletonOp& op) const
{
  return TypeNodeHashFunction()(op.getType());
}

SingletonOp::SingletonOp(const TypeNode& elementType)
    : d_type(new TypeNode(elementType))
{
}

SingletonOp::SingletonOp(const SingletonOp& op)
    : d_type(new TypeNode(op.getType()))
{
}

const TypeNode& SingletonOp::getType() const { return *d_type; }

bool SingletonOp::operator==(const SingletonOp& op) const
{
  return getType() == op.getType();
}

}  // namespace CVC4

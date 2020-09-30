/*********************                                                        */
/*! \file singleton.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/singleton_type.h"

#include <iostream>

#include "expr/type_node.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const SingletonType& asa) {
  return out << "(singleton_type " << asa.getType() << ')';
}

size_t SingletonTypeHashFunction::operator()(const SingletonType& es) const {
  return TypeNodeHashFunction()(es.getType());
}

/**
 * Constructs an singleton of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
SingletonType::SingletonType(const TypeNode& setType) : d_type(new TypeNode(setType)) {}

SingletonType::SingletonType(const SingletonType& es) : d_type(new TypeNode(es.getType())) {}

SingletonType& SingletonType::operator=(const SingletonType& es) {
  (*d_type) = es.getType();
  return *this;
}

SingletonType::~SingletonType() {}
const TypeNode& SingletonType::getType() const { return *d_type; }
bool SingletonType::operator==(const SingletonType& es) const
{
  return getType() == es.getType();
}

bool SingletonType::operator!=(const SingletonType& es) const { return !(*this == es); }
bool SingletonType::operator<(const SingletonType& es) const
{
  return getType() < es.getType();
}

bool SingletonType::operator<=(const SingletonType& es) const
{
  return getType() <= es.getType();
}

bool SingletonType::operator>(const SingletonType& es) const { return !(*this <= es); }
bool SingletonType::operator>=(const SingletonType& es) const { return !(*this < es); }
}/* CVC4 namespace */

/*********************                                                        */
/*! \file array_store_all.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of a constant array (an array in which the
 ** element is the same for all indices)
 **
 ** Representation of a constant array (an array in which the element is
 ** the same for all indices).
 **/

#include "expr/array_store_all.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "expr/type_node.h"

using namespace std;

namespace CVC4 {

ArrayStoreAll::ArrayStoreAll(const TypeNode& type, const Node& value)
    : d_type(), d_value()
{
  // this check is stronger than the assertion check in the expr manager that
  // ArrayTypes are actually array types
  // because this check is done in production builds too
  PrettyCheckArgument(
      type.isArray(), type,
      "array store-all constants can only be created for array types, not `%s'",
      type.toString().c_str());

  PrettyCheckArgument(
      value.getType().isComparableTo(type.getArrayConstituentType()),
      value,
      "expr type `%s' does not match constituent type of array type `%s'",
      value.getType().toString().c_str(),
      type.toString().c_str());

  PrettyCheckArgument(
      value.isConst(), value, "ArrayStoreAll requires a constant expression");

  // Delay allocation until the checks above have been performed. If these
  // fail, the memory for d_type and d_value should not leak. The alternative
  // is catch, delete and re-throw.
  d_type.reset(new TypeNode(type));
  d_value.reset(new Node(value));
}

ArrayStoreAll::ArrayStoreAll(const ArrayStoreAll& other)
    : d_type(new TypeNode(other.getType())), d_value(new Node(other.getValue()))
{
}

ArrayStoreAll::~ArrayStoreAll() {}
ArrayStoreAll& ArrayStoreAll::operator=(const ArrayStoreAll& other) {
  (*d_type) = other.getType();
  (*d_value) = other.getValue();
  return *this;
}

const TypeNode& ArrayStoreAll::getType() const { return *d_type; }

const Node& ArrayStoreAll::getValue() const { return *d_value; }

bool ArrayStoreAll::operator==(const ArrayStoreAll& asa) const
{
  return getType() == asa.getType() && getValue() == asa.getValue();
}

bool ArrayStoreAll::operator!=(const ArrayStoreAll& asa) const
{
  return !(*this == asa);
}

bool ArrayStoreAll::operator<(const ArrayStoreAll& asa) const
{
  return (getType() < asa.getType())
         || (getType() == asa.getType() && getValue() < asa.getValue());
}

bool ArrayStoreAll::operator<=(const ArrayStoreAll& asa) const
{
  return (getType() < asa.getType())
         || (getType() == asa.getType() && getValue() <= asa.getValue());
}

bool ArrayStoreAll::operator>(const ArrayStoreAll& asa) const
{
  return !(*this <= asa);
}

bool ArrayStoreAll::operator>=(const ArrayStoreAll& asa) const
{
  return !(*this < asa);
}

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa) {
  return out << "__array_store_all__(" << asa.getType() << ", "
             << asa.getValue() << ')';
}

size_t ArrayStoreAllHashFunction::operator()(const ArrayStoreAll& asa) const {
  return TypeNodeHashFunction()(asa.getType())
         * NodeHashFunction()(asa.getValue());
}

}  // namespace CVC4

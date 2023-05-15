/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of a constant array (an array in which the element is the
 * same for all indices).
 */

#include "expr/array_store_all.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5::internal {

ArrayStoreAll::ArrayStoreAll(const TypeNode& type, const Node& value)
    : d_type(), d_value()
{
  // this check is stronger than the assertion check in the expr manager that
  // ArrayTypes are actually array types
  // because this check is done in production builds too
  Assert(type.isArray())
      << "array store-all constants can only be created for array types, not `"
      << type.toString().c_str() << "'";
  Assert(value.getType() == type.getArrayConstituentType())
      << "expr type `" << value.getType().toString().c_str()
      << "' does not match constituent type of array type `"
      << type.toString().c_str() << "'";
  Trace("arrays") << "constructing constant array of type: '" << type
                  << "' and value: '" << value << "'" << std::endl;
  Assert(value.isConst()) << "ArrayStoreAll requires a constant expression";

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
  return std::hash<TypeNode>()(asa.getType())
         * std::hash<Node>()(asa.getValue());
}

}  // namespace cvc5::internal

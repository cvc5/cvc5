/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of abstract values.
 */

#include "util/abstract_value.h"

#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const AbstractValue& val) {
  return out << "@a" << val.getIndex();
}

AbstractValue::AbstractValue(const TypeNode& type, const Integer& index)
    : d_type(new TypeNode(type)), d_index(index)
{
  PrettyCheckArgument(index >= 0,
                      index,
                      "index >= 0 required for abstract value, not `%s'",
                      index.toString().c_str());
}

AbstractValue::AbstractValue(const AbstractValue& val)
    : d_type(new TypeNode(*val.d_type)), d_index(val.d_index)
{
}

AbstractValue::~AbstractValue() {}

const TypeNode& AbstractValue::getType() const { return *d_type; }

bool AbstractValue::operator==(const AbstractValue& val) const
{
  return getType() == val.getType() && d_index == val.d_index;
}

bool AbstractValue::operator<(const AbstractValue& val) const
{
  return getType() < val.getType()
         || (getType() == val.getType() && d_index < val.d_index);
}

bool AbstractValue::operator<=(const AbstractValue& val) const
{
  return getType() <= val.getType()
         || (getType() == val.getType() && d_index <= val.d_index);
}

}  // namespace cvc5

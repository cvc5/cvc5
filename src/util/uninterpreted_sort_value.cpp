/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of abstract values.
 */

#include "util/uninterpreted_sort_value.h"

#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const UninterpretedSortValue& val)
{
  return out << "@" << val.getType() << "_" << val.getIndex();
}

UninterpretedSortValue::UninterpretedSortValue(const TypeNode& type,
                                               const Integer& index)
    : d_type(new TypeNode(type)), d_index(index)
{
  Assert(type.isUninterpretedSort())
      << "uninterpreted constants can only be created for "
         "uninterpreted sorts, not `"
      << type.toString().c_str() << "'";
  Assert(index >= 0) << "index >= 0 required for abstract value, not `"
                     << index.toString().c_str() << "'";
}

UninterpretedSortValue::UninterpretedSortValue(
    const UninterpretedSortValue& val)
    : d_type(new TypeNode(*val.d_type)), d_index(val.d_index)
{
}

UninterpretedSortValue::~UninterpretedSortValue() {}

const TypeNode& UninterpretedSortValue::getType() const { return *d_type; }

bool UninterpretedSortValue::operator==(const UninterpretedSortValue& val) const
{
  return getType() == val.getType() && d_index == val.d_index;
}

bool UninterpretedSortValue::operator<(const UninterpretedSortValue& val) const
{
  return getType() < val.getType()
         || (getType() == val.getType() && d_index < val.d_index);
}

bool UninterpretedSortValue::operator<=(const UninterpretedSortValue& val) const
{
  return getType() <= val.getType()
         || (getType() == val.getType() && d_index <= val.d_index);
}

}  // namespace cvc5::internal

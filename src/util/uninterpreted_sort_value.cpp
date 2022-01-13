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

#include "util/uninterpreted_sort_value.h"

#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const UninterpretedSortValue& val)
{
  return out << "@a" << val.getIndex();
}

UninterpretedSortValue::UninterpretedSortValue(const TypeNode& type,
                                               const Integer& index)
    : d_type(new TypeNode(type)), d_index(index)
{
  PrettyCheckArgument(type.isSort(),
                      type,
                      "uninterpreted constants can only be created for "
                      "uninterpreted sorts, not `%s'",
                      type.toString().c_str());
  PrettyCheckArgument(index >= 0,
                      index,
                      "index >= 0 required for abstract value, not `%s'",
                      index.toString().c_str());
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

}  // namespace cvc5

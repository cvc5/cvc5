/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of an almost constant function
 */

#include "expr/function_const.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"

using namespace std;

namespace cvc5::internal {

FunctionConst::FunctionConst(const Node& value)
    :  d_value()
{
  d_value.reset(new Node(value));
}

FunctionConst::FunctionConst(const FunctionConst& other)
    : d_value(new Node(other.getValue()))
{
}

FunctionConst::~FunctionConst() {}
FunctionConst& FunctionConst::operator=(const FunctionConst& other) {
  (*d_value) = other.getValue();
  return *this;
}

const TypeNode& FunctionConst::getType() const { 
  TypeNode tn = d_value->getType();
  // TODO
  return tn;
}

const Node& FunctionConst::getValue() const { return *d_value; }

bool FunctionConst::operator==(const FunctionConst& fc) const
{
  return getValue() == fc.getValue();
}

bool FunctionConst::operator!=(const FunctionConst& fc) const
{
  return !(*this == fc);
}

bool FunctionConst::operator<(const FunctionConst& fc) const
{
  return getValue() < fc.getValue();
}

bool FunctionConst::operator<=(const FunctionConst& fc) const
{
  return getValue() <= fc.getValue();
}

bool FunctionConst::operator>(const FunctionConst& fc) const
{
  return !(*this <= fc);
}

bool FunctionConst::operator>=(const FunctionConst& fc) const
{
  return !(*this < fc);
}

std::ostream& operator<<(std::ostream& out, const FunctionConst& fc) {
  return out << "__function_const(" << fc.getValue() << ")";
}

size_t FunctionConstHashFunction::operator()(const FunctionConst& fc) const {
  return std::hash<Node>()(fc.getValue());
}

}  // namespace cvc5::internal

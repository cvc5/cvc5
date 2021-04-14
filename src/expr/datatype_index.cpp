/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing an index to a datatype living in NodeManager.
 */
#include "expr/datatype_index.h"

#include <sstream>
#include <string>
#include "util/hash.h"
#include "util/integer.h"

using namespace std;

namespace cvc5 {

DatatypeIndexConstant::DatatypeIndexConstant(uint32_t index) : d_index(index) {}
std::ostream& operator<<(std::ostream& out, const DatatypeIndexConstant& dic)
{
  return out << "index_" << dic.getIndex();
}

size_t DatatypeIndexConstantHashFunction::operator()(
    const DatatypeIndexConstant& dic) const
{
  return IntegerHashFunction()(dic.getIndex());
}

}  // namespace cvc5

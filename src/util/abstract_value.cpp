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

using namespace std;

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const AbstractValue& val) {
  return out << "@" << val.getIndex();
}

AbstractValue::AbstractValue(Integer index) : d_index(index)
{
  PrettyCheckArgument(index >= 1,
                      index,
                      "index >= 1 required for abstract value, not `%s'",
                      index.toString().c_str());
}

}  // namespace cvc5

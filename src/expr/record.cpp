/******************************************************************************
 * Top contributors (to current version):
 *   Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a record definition.
 */

#include "expr/record.h"

#include "base/check.h"
#include "base/output.h"

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) {
  return out << "[" << t.getField() << "]";
}

}  // namespace cvc5

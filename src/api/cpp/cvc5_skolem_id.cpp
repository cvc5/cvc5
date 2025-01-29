/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of skolem id.
 */

#include <cvc5/cvc5_skolem_id.h>

#include <iostream>

#include "printer/enum_to_string.h"

namespace std {

std::string to_string(cvc5::SkolemId id)
{
  return cvc5::internal::toString(id);
}
}  // namespace std

namespace cvc5 {

std::ostream& operator<<(std::ostream& out, SkolemId id)
{
  out << std::to_string(id);
  return out;
}
}  // namespace cvc5

namespace std {

size_t hash<cvc5::SkolemId>::operator()(cvc5::SkolemId id) const
{
  return static_cast<size_t>(id);
}

}  // namespace std

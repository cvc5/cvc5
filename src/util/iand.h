/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The integer AND operator.
 */

#include "cvc5_public.h"

#ifndef CVC5__IAND_H
#define CVC5__IAND_H

#include <iosfwd>

#include "base/exception.h"
#include "util/integer.h"

namespace cvc5 {

struct IntAnd
{
  unsigned d_size;
  IntAnd(unsigned size) : d_size(size) {}
  operator unsigned() const { return d_size; }
}; /* struct IntAnd */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia);
inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia)
{
  return os << "(_ iand " << ia.d_size << ")";
}

}  // namespace cvc5

#endif /* CVC5__IAND_H */

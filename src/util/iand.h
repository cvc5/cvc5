/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Yoni Zohar
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

struct IntAnd
{
  uint32_t d_size;
  IntAnd(uint32_t size) : d_size(size) {}
  operator uint32_t() const { return d_size; }
}; /* struct IntAnd */

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia);
inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia)
{
  return os << "(_ iand " << ia.d_size << ")";
}

}  // namespace cvc5::internal

#endif /* CVC5__IAND_H */

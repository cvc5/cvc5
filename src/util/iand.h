/*********************                                                        */
/*! \file iand.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The integer AND operator.
 **/

#include "cvc4_public.h"

#ifndef CVC4__IAND_H
#define CVC4__IAND_H

#include <cstdint>
#include <iosfwd>

#include "base/exception.h"
#include "util/integer.h"

namespace CVC4 {

struct CVC4_PUBLIC IntAnd
{
  unsigned d_size;
  IntAnd(unsigned size) : d_size(size) {}
  operator unsigned() const { return d_size; }
}; /* struct IntAnd */

/* -----------------------------------------------------------------------
 ** Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const IntAnd& ia)
{
  return os << "[" << ia.d_size << "]";
}

}  // namespace CVC4

#endif /* CVC4__IAND_H */

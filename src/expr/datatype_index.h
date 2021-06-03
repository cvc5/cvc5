/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Mathias Preiner
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

#include "cvc5_public.h"

#ifndef CVC5__DATATYPE_INDEX_H
#define CVC5__DATATYPE_INDEX_H

#include <iosfwd>

namespace cvc5 {

/* stores an index to Datatype residing in NodeManager */
class DatatypeIndexConstant
{
 public:
  DatatypeIndexConstant(unsigned index);

  unsigned getIndex() const { return d_index; }
  bool operator==(const DatatypeIndexConstant& uc) const
  {
    return d_index == uc.d_index;
  }
  bool operator!=(const DatatypeIndexConstant& uc) const
  {
    return !(*this == uc);
  }
  bool operator<(const DatatypeIndexConstant& uc) const
  {
    return d_index < uc.d_index;
  }
  bool operator<=(const DatatypeIndexConstant& uc) const
  {
    return d_index <= uc.d_index;
  }
  bool operator>(const DatatypeIndexConstant& uc) const
  {
    return !(*this <= uc);
  }
  bool operator>=(const DatatypeIndexConstant& uc) const
  {
    return !(*this < uc);
  }

 private:
  const unsigned d_index;
}; /* class DatatypeIndexConstant */

std::ostream& operator<<(std::ostream& out, const DatatypeIndexConstant& dic);

struct DatatypeIndexConstantHashFunction
{
  size_t operator()(const DatatypeIndexConstant& dic) const;
}; /* struct DatatypeIndexConstantHashFunction */

}  // namespace cvc5

#endif /* CVC5__DATATYPE_H */

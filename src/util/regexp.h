/*********************                                                        */
/*! \file regexp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Data structures for regular expression operators.
 **/

#include "cvc4_public.h"

#ifndef CVC4__UTIL__REGEXP_H
#define CVC4__UTIL__REGEXP_H

#include <cstdint>
#include <iosfwd>

namespace CVC4 {

struct CVC4_PUBLIC RegExpRepeat
{
  uint32_t d_repeatAmount;
  RegExpRepeat(uint32_t repeatAmount) : d_repeatAmount(repeatAmount) {}

  bool operator==(const RegExpRepeat& r) const
  {
    return d_repeatAmount == r.d_repeatAmount;
  }
};

struct CVC4_PUBLIC RegExpLoop
{
  unsigned d_loopAmountLo;
  unsigned d_loopAmountHi;
  RegExpLoop(unsigned l, unsigned h) : d_loopAmountLo(l), d_loopAmountHi(h) {}

  bool operator==(const RegExpLoop& r) const
  {
    return d_loopAmountLo == r.d_loopAmountLo
           && d_loopAmountHi == r.d_loopAmountHi;
  }
};

/* -----------------------------------------------------------------------
 ** Hash Function structs
 * ----------------------------------------------------------------------- */

/*
 * Hash function for the RegExpRepeat constants.
 */
struct CVC4_PUBLIC RegExpRepeatHashFunction
{
  inline size_t operator()(const RegExpRepeat& r) const
  {
    return r.d_repeatAmount;
  }
};

/**
 * Hash function for the RegExpLoop objects.
 */
struct CVC4_PUBLIC RegExpLoopHashFunction
{
  size_t operator()(const RegExpLoop& r) const
  {
    return r.d_loopAmountLo + r.d_loopAmountHi;
  }
};

/* -----------------------------------------------------------------------
 ** Output stream
 * ----------------------------------------------------------------------- */

inline std::ostream& operator<<(std::ostream& os,
                                const RegExpRepeat& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const RegExpRepeat& r)
{
  return os << r.d_repeatAmount;
}

inline std::ostream& operator<<(std::ostream& os,
                                const RegExpLoop& bv) CVC4_PUBLIC;
inline std::ostream& operator<<(std::ostream& os, const RegExpLoop& r)
{
  return os << "[" << r.d_loopAmountLo << ":" << r.d_loopAmountHi << "]";
}

}  // namespace CVC4

#endif /* CVC4__UTIL__REGEXP_H */

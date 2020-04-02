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
  RegExpRepeat(uint32_t repeatAmount);

  bool operator==(const RegExpRepeat& r) const;
  /** The amount of repetitions of the regular expression */
  uint32_t d_repeatAmount;
};

struct CVC4_PUBLIC RegExpLoop
{
  RegExpLoop(uint32_t l, uint32_t h);

  bool operator==(const RegExpLoop& r) const;
  /** The minimum number of repetitions of the regular expression */
  uint32_t d_loopMinOcc;
  /** The maximum number of repetitions of the regular expression */
  uint32_t d_loopMaxOcc;
};

/* -----------------------------------------------------------------------
 ** Hash Function structs
 * ----------------------------------------------------------------------- */

/*
 * Hash function for the RegExpRepeat constants.
 */
struct CVC4_PUBLIC RegExpRepeatHashFunction
{
  size_t operator()(const RegExpRepeat& r) const;
};

/**
 * Hash function for the RegExpLoop objects.
 */
struct CVC4_PUBLIC RegExpLoopHashFunction
{
  size_t operator()(const RegExpLoop& r) const;
};

/* -----------------------------------------------------------------------
 ** Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const RegExpRepeat& bv) CVC4_PUBLIC;

std::ostream& operator<<(std::ostream& os, const RegExpLoop& bv) CVC4_PUBLIC;

}  // namespace CVC4

#endif /* CVC4__UTIL__REGEXP_H */

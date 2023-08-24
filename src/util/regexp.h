/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Data structures for regular expression operators.
 */

#include "cvc5_public.h"

#ifndef CVC5__UTIL__REGEXP_H
#define CVC5__UTIL__REGEXP_H

#include <iosfwd>

namespace cvc5::internal {

struct RegExpRepeat
{
  RegExpRepeat(uint32_t repeatAmount);

  bool operator==(const RegExpRepeat& r) const;
  /** The amount of repetitions of the regular expression */
  uint32_t d_repeatAmount;
};

struct RegExpLoop
{
  RegExpLoop(uint32_t l, uint32_t h);

  bool operator==(const RegExpLoop& r) const;
  /** The minimum number of repetitions of the regular expression */
  uint32_t d_loopMinOcc;
  /** The maximum number of repetitions of the regular expression */
  uint32_t d_loopMaxOcc;
};

/* -----------------------------------------------------------------------
 * Hash Function structs
 * ----------------------------------------------------------------------- */

/*
 * Hash function for the RegExpRepeat constants.
 */
struct RegExpRepeatHashFunction
{
  size_t operator()(const RegExpRepeat& r) const;
};

/**
 * Hash function for the RegExpLoop objects.
 */
struct RegExpLoopHashFunction
{
  size_t operator()(const RegExpLoop& r) const;
};

/* -----------------------------------------------------------------------
 * Output stream
 * ----------------------------------------------------------------------- */

std::ostream& operator<<(std::ostream& os, const RegExpRepeat& bv);

std::ostream& operator<<(std::ostream& os, const RegExpLoop& bv);

}  // namespace cvc5::internal

#endif /* CVC5__UTIL__REGEXP_H */

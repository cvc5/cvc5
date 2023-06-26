/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A bitmap of Kinds.
 *
 * This is a class representation for a bitmap of Kinds that is iterable,
 * manipulable, and packed.
 */

#include "cvc5_private.h"

#ifndef CVC5__KIND_MAP_H
#define CVC5__KIND_MAP_H

#include <bitset>

#include "base/check.h"
#include "expr/kind.h"

namespace cvc5::internal {

/** A very simple bitmap for Kinds */
class KindMap
{
 public:
  /** Set the bit for k */
  void set(Kind k) { d_bits.set(fromKind(k)); }
  /** Reset the bit for k */
  void reset(Kind k) { d_bits.reset(fromKind(k)); }
  /** Check whether the bit for k is set */
  bool test(Kind k) const { return d_bits.test(fromKind(k)); }
  /** Check whether the bit for k is set */
  bool operator[](Kind k) const { return test(k); }

 private:
  /** Convert kind to std::size_t and check bounds */
  static std::size_t fromKind(Kind k)
  {
    AssertArgument(k >= Kind(0) && k < kind::LAST_KIND, k, "invalid kind");
    return static_cast<std::size_t>(k);
  }
  /** The bitmap */
  std::bitset<kind::LAST_KIND> d_bits;
};

}  // namespace cvc5::internal

#endif /* CVC5__KIND_MAP_H */

/*********************                                                        */
/*! \file theory_id.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Aina Niemetz, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef CVC4__THEORY__THEORY_ID_H
#define CVC4__THEORY__THEORY_ID_H

#include <iostream>

namespace CVC4 {
namespace theory {

/**
 * IMPORTANT: The order of the theories is important. For example, strings
 *            depends on arith, quantifiers needs to come as the very last.
 *            Do not change this order.
 */
enum TheoryId
{
  THEORY_BUILTIN,
  THEORY_BOOL,
  THEORY_UF,
  THEORY_ARITH,
  THEORY_BV,
  THEORY_FP,
  THEORY_ARRAYS,
  THEORY_DATATYPES,
  THEORY_SEP,
  THEORY_SETS,
  THEORY_BAGS,
  THEORY_STRINGS,
  THEORY_QUANTIFIERS,

  THEORY_LAST
};

const TheoryId THEORY_FIRST = static_cast<TheoryId>(0);
const TheoryId THEORY_SAT_SOLVER = THEORY_LAST;

TheoryId& operator++(TheoryId& id) CVC4_PUBLIC;

std::ostream& operator<<(std::ostream& out, TheoryId theoryId);

std::string getStatsPrefix(TheoryId theoryId) CVC4_PUBLIC;

/**
 * A set of theories. Utilities for TheoryIdSet can be found below.
 */
typedef uint32_t TheoryIdSet;

class TheoryIdSetUtil
{
 public:
  /** A set of all theories */
  static const TheoryIdSet AllTheories = (1 << theory::THEORY_LAST) - 1;

  /** Pops a first theory off the set */
  static TheoryId setPop(TheoryIdSet& set);

  /** Returns the size of a set of theories */
  static size_t setSize(TheoryIdSet set);

  /** Returns the index size of a set of theories */
  static size_t setIndex(TheoryId id, TheoryIdSet set);

  /** Add the theory to the set. If no set specified, just returns a singleton
   * set */
  static TheoryIdSet setInsert(TheoryId theory, TheoryIdSet set = 0);

  /** Add the theory to the set. If no set specified, just returns a singleton
   * set */
  static TheoryIdSet setRemove(TheoryId theory, TheoryIdSet set = 0);

  /** Check if the set contains the theory */
  static bool setContains(TheoryId theory, TheoryIdSet set);

  /** Set complement of a */
  static TheoryIdSet setComplement(TheoryIdSet a);

  /** Set intersection of a and b */
  static TheoryIdSet setIntersection(TheoryIdSet a, TheoryIdSet b);

  /** Set union of a and b */
  static TheoryIdSet setUnion(TheoryIdSet a, TheoryIdSet b);

  /** Set difference of a and b */
  static TheoryIdSet setDifference(TheoryIdSet a, TheoryIdSet b);

  /** Convert theorySet to string (for debugging) */
  static std::string setToString(TheoryIdSet theorySet);
};

}  // namespace theory
}  // namespace CVC4
#endif

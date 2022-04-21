/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Info per pattern term in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__MATCH_PAT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__MATCH_PAT_INFO_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

/**
 * Data for matching a pattern term at a fixed context level. For details,
 * see matching.h.
 */
class MatchPatInfo
{
 public:
  MatchPatInfo();
  /**
   * Add watched equivalence class, which is an equivalence class that might
   * be relevant for matching.
   */
  void addWatchEqc(TNode eqc);
  /** Get the next watched eqc, increment the watched counter. */
  TNode getNextWatchEqc();
  /** Set that it is possible that this pattern can be equal to eqc. */
  void addMaybeEqc(TNode eqc);
  /**
   * Is this pattern maybe equal to eqc? Returns true if this pattern is
   * a bound variable, or if eqc was added via addMaybeEqc.
   *
   * This method should be called on eqc that we have processed as watched
   * equivalence classes (those for which getNextWatchEqc has returned eqc).
   * If this returns false, then the pattern of this class will never be
   * equal to eqc.
   */
  bool isMaybeEqc(TNode eqc) const;

 private:
  /**
   * Watched equivalence classes. This is the set of equivalence classes that
   * may be relevant if this pattern is equal.
   */
  std::unordered_set<TNode> d_watchEqc;
  /** List we are procesing */
  std::vector<TNode> d_watchEqcList;
  /**
   * Watched equivalence classes we have processed.
   * - If pattern is variable, this is the index we have tried
   * - Otherwise, this is the index in the
   */
  size_t d_watchEqcIndex;
  /**
   * Maybe equal to, which is a subset of d_watchEqc.
   *
   * The equivalence classes we have processed in d_watchEqc that are not in
   * d_maybeEqc are such that this pattern will never merge with.
   */
  std::unordered_set<TNode> d_maybeEqc;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif

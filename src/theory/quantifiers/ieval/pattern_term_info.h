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
 * Info per pattern term in instantiation evaluator.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__IEVAL__PATTERN_TERM_INFO_H
#define CVC5__THEORY__QUANTIFIERS__IEVAL__PATTERN_TERM_INFO_H

#include <map>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/ieval/term_evaluator_callback.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;

namespace ieval {

class State;

/**
 * A quantified formula is a pattern term whose parent is
 * the quant
 */
class PatTermInfo
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  PatTermInfo(context::Context* c);
  /** initialize */
  void initialize(TNode pattern, TermDb* tdb);
  /** Reset round */
  void resetRound();
  /**
   * is active, false if it has merged to a ground equivalence class, or if
   * its variables have been fully assigned.
   */
  bool isActive() const;
  /**
   * Notify that child was assigned value val, set eq if possible.
   * Return true if we set eq during this call.
   *
   * This call is not responsible for notifying parents.
   */
  bool notifyChild(State& s,
                   TNode child,
                   TNode val,
                   TermEvaluatorCallback* tec);
  /** This pattern term. */
  TNode d_pattern;
  /** The match operator */
  TNode d_matchOp;
  //---------------------- during search
  /**
   * The ground term we are currently equal to, if any. This may also be
   * the none node.
   */
  context::CDO<TNode> d_eq;
  /** The number of unassigned children (for Boolean connectives). */
  context::CDO<size_t> d_numUnassigned;
  /** Number of unique children */
  size_t d_numChildren;
  /**
   * The list of pattern terms that are the parent of this. For pattern p,
   * this is either:
   * (1) A term of the form f( ... p ... ), where f may be a Boolean connective.
   * (2) A quantified formula Q whose body has p as a disjunct.
   */
  NodeList d_parentNotify;
  /**
   * Are we watching whether to evaluate this term?
   */
  context::CDO<bool> d_isWatchedEval;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

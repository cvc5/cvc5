/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace ieval {

class State;
class TermEvaluator;

/**
 * Information for a pattern term in the instantiation evaluator. This
 * tracks what term the pattern is currently entailed to be equal to,
 * and the child (if any) that explains why it is.
 */
class PatTermInfo
{
  using NodeList = context::CDList<Node>;

 public:
  PatTermInfo(context::Context* c);
  /** initialize */
  void initialize(TNode pattern);
  /** Reset round */
  void resetRound();
  /**
   * Is active, return false if d_eq has been set to a ground term, possibly
   * the "none" term (indicating that this pattern is not entailed to be equal
   * to any known ground term).
   */
  bool isActive() const;
  /**
   * Notify that child was assigned value val, set d_eq if possible.
   * Return true if we set eq during this call.
   *
   * This call is not responsible for notifying parents.
   */
  bool notifyChild(State& s, TNode child, TNode val, TermEvaluator* tec);
  /** This pattern term. */
  TNode d_pattern;
  //---------------------- during search
  /**
   * The ground term we are currently equal to, if any. This may also be
   * the none node.
   */
  context::CDO<TNode> d_eq;
  /** The number of unassigned children. */
  context::CDO<size_t> d_numUnassigned;
  /**
   * The list of pattern terms that are the parent of this. For pattern p,
   * this is either:
   * (1) A term of the form f( ... p ... ), where f may be a Boolean connective.
   * (2) A quantified formula Q whose body has p as a disjunct.
   */
  NodeList d_parentNotify;
  /**
   * The child that caused us to evaluate, which is used for tracking
   * explanations. If this is null and d_eq is non-null, then we assume that
   * all children were required for evaluation.
   *
   * Note that a more advanced implementation could track a subset of children
   * used for evaluation, which we don't consider here. Instead, for simplicity,
   * we only consider cases where a single child forced the evaluation.
   */
  context::CDO<TNode> d_evalExpChild;
};

}  // namespace ieval
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trigger term info class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TRIGGER_TERM_INFO_H
#define CVC5__THEORY__QUANTIFIERS__TRIGGER_TERM_INFO_H

#include <map>

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** Information about a node used in a trigger.
 *
 * This information includes:
 * 1. the free variables of the node, and
 * 2. information about which terms are useful for matching.
 *
 * As an example, consider the trigger
 *   { f( x ), g( y ), P( y, z ) }
 * for quantified formula
 *   forall xy. ( f( x ) != b => ( P( x, g( y ) ) V P( y, z ) ) )
 *
 * Notice that it is only useful to match f( x ) to f-applications not in the
 * equivalence class of b, and P( y, z ) to P-applications not in the
 * equivalence class of true, as such instances will always be entailed by the
 * ground equalities and disequalities the current context. Entailed instances
 * are typically not helpful, and are discarded in
 * Instantiate::addInstantiation(...) unless the option --no-inst-no-entail is
 * enabled. For more details, see page 10 of "Congruence Closure with Free
 * Variables", Barbosa et al., TACAS 2017.
 *
 * This example is referenced for each of the functions below.
 */
class TriggerTermInfo
{
 public:
  TriggerTermInfo() : d_reqPol(0), d_weight(0) {}
  ~TriggerTermInfo() {}
  /** The free variables in the node
   *
   * In the trigger term info for f( x ) in the above example, d_fv = { x }
   * In the trigger term info for g( y ) in the above example, d_fv = { y }
   * In the trigger term info for P( y, z ) in the above example, d_fv = { y, z
   * }
   */
  std::vector<Node> d_fv;
  /** Required polarity:  1 for equality, -1 for disequality, 0 for none
   *
   * In the trigger term info for f( x ) in the above example, d_reqPol = -1
   * In the trigger term info for g( y ) in the above example, d_reqPol = 0
   * In the trigger term info for P( y, z ) in the above example,  d_reqPol = 1
   */
  int d_reqPol;
  /** Required polarity equal term
   *
   * If d_reqPolEq is not null,
   *   if d_reqPol = 1, then this trigger term must be matched to terms in the
   *                    equivalence class of d_reqPolEq,
   *   if d_reqPol = -1, then this trigger term must be matched to terms *not*
   * in the equivalence class of d_reqPolEq.
   *
   * This information is typically chosen by analyzing the entailed equalities
   * and disequalities of quantified formulas.
   * In the trigger term info for f( x ) in the above example, d_reqPolEq = b
   * In the trigger term info for g( y ) in the above example,
   *   d_reqPolEq = Node::null()
   * In the trigger term info for P( y, z ) in the above example,
   *   d_reqPolEq = false
   */
  Node d_reqPolEq;
  /** the weight of the trigger (see getTriggerWeight). */
  int32_t d_weight;
  /** Initialize this information class (can be called more than once).
   * q is the quantified formula that n is a trigger term for
   * n is the trigger term
   * reqPol/reqPolEq are described above
   */
  void init(Node q, Node n, int reqPol = 0, Node reqPolEq = Node::null());
  /** is n an atomic trigger?
   *
   * An atomic trigger is one whose kind is an atomic trigger kind.
   */
  static bool isAtomicTrigger(Node n);
  /** Is k an atomic trigger kind?
   *
   * An atomic trigger kind is one for which term indexing/matching is possible.
   */
  static bool isAtomicTriggerKind(Kind k);
  /** is n a relational trigger, e.g. like x >= a ? */
  static bool isRelationalTrigger(Node n);
  /** Is k a relational trigger kind? */
  static bool isRelationalTriggerKind(Kind k);
  /**
   * Is n a usable relational trigger, which is true if RelationalMatchGenerator
   * can process n.
   */
  static bool isUsableRelationTrigger(Node n);
  /**
   * Same as above, but lit / hasPol / pol are updated to the required
   * constructor arguments for RelationalMatchGenerator.
   */
  static bool isUsableRelationTrigger(Node n,
                                      bool& hasPol,
                                      bool& pol,
                                      Node& lit);
  /** is n a simple trigger (see inst_match_generator.h)? */
  static bool isSimpleTrigger(Node n);
  /** get trigger weight
   *
   * Intutively, this function classifies how difficult it is to handle the
   * trigger term n, where the smaller the value, the easier.
   *
   * Returns 0 for triggers that are APPLY_UF terms.
   * Returns 1 for other triggers whose kind is atomic, or are usable
   * relational triggers.
   * Returns 2 otherwise.
   */
  static int32_t getTriggerWeight(Node n);
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

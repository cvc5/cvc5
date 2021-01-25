/*********************                                                        */
/*! \file trigger_term_info.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger term info class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TRIGGER_TERM_INFO_H
#define CVC4__THEORY__QUANTIFIERS__TRIGGER_TERM_INFO_H

#include <map>

#include "expr/node.h"

namespace CVC4 {
namespace theory {
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
  /** the weight of the trigger (see Trigger::getTriggerWeight). */
  int d_weight;
  /** Initialize this information class (can be called more than once).
   * q is the quantified formula that n is a trigger term for
   * n is the trigger term
   * reqPol/reqPolEq are described above
   */
  void init(Node q, Node n, int reqPol = 0, Node reqPolEq = Node::null());
};

}  // namespace inst
}  // namespace theory
}  // namespace CVC4

#endif

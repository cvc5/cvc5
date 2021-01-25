/*********************                                                        */
/*! \file pattern_term_selector.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief pattern term selector class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__PATTERN_TERM_SELECTOR_H
#define CVC4__THEORY__QUANTIFIERS__PATTERN_TERM_SELECTOR_H

#include <map>

#include "expr/node.h"
#include "options/quantifiers_options.h"

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

/**
 * Pattern term selector, which is responsible for constructing a pool of terms,
 * generally based on the body of a quantified formula, which is then used for
 * selecting triggers.
 */
class PatternTermSelector
{
 public:
  PatternTermSelector(Node q);
  ~PatternTermSelector();
  /** collect pattern terms
   *
   * This collects all terms that are eligible for triggers for the quantified
   * formula of this class in term n and adds them to patTerms.
   *   tstrt : the selection strategy (see options/quantifiers_mode.h),
   *   exclude :  a set of terms that *cannot* be selected as triggers,
   *   tinfo : stores the result of the collection, mapping terms to the
   *           information they are associated with,
   *   filterInst : flag that when true, we discard terms that have instances
   *     in the vector we are returning, e.g. we do not return f( x ) if we are
   *     also returning f( f( x ) ). TODO: revisit this (issue #1211)
   */
  void collectTerms(Node n,
                    std::vector<Node>& patTerms,
                    options::TriggerSelMode tstrt,
                    std::vector<Node>& exclude,
                    std::map<Node, TriggerTermInfo>& tinfo,
                    bool filterInst = false);
  /** Is n a usable trigger in quantified formula q?
   *
   * A usable trigger is one that is matchable and contains free variables only
   * from q.
   */
  static bool isUsableTrigger(Node n, Node q);
  /** get is usable trigger
   *
   * Return the associated node of n that is a usable trigger in quantified
   * formula q. This may be different than n in several cases :
   * (1) Polarity information is explicitly converted to equalities, e.g.
   *      getIsUsableTrigger( (not (P x )), q ) may return (= (P x) false)
   * (2) Relational triggers are put into solved form, e.g.
   *      getIsUsableTrigger( (= (+ x a) 5), q ) may return (= x (- 5 a)).
   */
  static Node getIsUsableTrigger(Node n, Node q);
  /** Is n a usable atomic trigger?
   *
   * A usable atomic trigger is a term that is both a useable trigger and an
   * atomic trigger.
   */
  static bool isUsableAtomicTrigger(Node n, Node q);
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
  /** get trigger weight
   *
   * Intutively, this function classifies how difficult it is to handle the
   * trigger term n, where the smaller the value, the easier.
   *
   * Returns 0 for triggers that are APPLY_UF terms.
   * Returns 1 for other triggers whose kind is atomic.
   * Returns 2 otherwise.
   */
  static int getTriggerWeight(Node n);
  /** get the variable associated with an inversion for n
   *
   * A term n with an inversion variable x has the following property :
   *   There exists a closed function f such that for all terms t
   *   |= (n = t) <=> (x = f(t))
   * For example, getInversionVariable( x+1 ) returns x since for all terms t,
   *   |= x+1 = t <=> x = (\y. y-1)(t)
   * We call f the inversion function for n.
   */
  static Node getInversionVariable(Node n);
  /** Get the body of the inversion function for n whose argument is y.
   * e.g. getInversion( x+1, y ) returns y-1
   */
  static Node getInversion(Node n, Node y);

 protected:
  /** is subterm of trigger usable (helper function for isUsableTrigger) */
  static bool isUsable(Node n, Node q);
  /** returns an equality that is equivalent to the equality eq and
   * is a usable trigger for q if one exists, otherwise returns Node::null().
   */
  static Node getIsUsableEq(Node q, Node eq);
  /** returns whether n1 == n2 is a usable (relational) trigger for q. */
  static bool isUsableEqTerms(Node q, Node n1, Node n2);
  /** recursive helper function for collectPatTerms
   *
   * This collects the usable trigger terms in the subterm n of the body of
   * quantified formula of this class.
   *   visited : cache of the trigger terms collected for each visited node,
   *   tinfo : cache of trigger term info for each visited node,
   *   tstrat : the selection strategy (see options/quantifiers_mode.h)
   *   exclude :  a set of terms that *cannot* be selected as triggers
   *   pol/hasPol : the polarity of node n in q
   *                (see QuantPhaseReq theory/quantifiers/quant_util.h)
   *   epol/hasEPol : the entailed polarity of node n in q
   *                  (see QuantPhaseReq theory/quantifiers/quant_util.h)
   *   knowIsUsable : whether we know that n is a usable trigger.
   *
   * We add the triggers we collected recursively in n into added.
   */
  void collectTermsInternal(Node n,
                            std::map<Node, std::vector<Node> >& visited,
                            std::map<Node, TriggerTermInfo>& tinfo,
                            options::TriggerSelMode tstrt,
                            std::vector<Node>& exclude,
                            std::vector<Node>& added,
                            bool pol,
                            bool hasPol,
                            bool epol,
                            bool hasEPol,
                            bool knowIsUsable = false);

  /** filter all nodes that have trigger instances
   *
   * This is used during collectModelInfo to filter certain trigger terms,
   * stored in nodes. This updates nodes so that no pairs of distinct nodes
   * (i,j) is such that i is a trigger instance of j or vice versa (see below).
   */
  static void filterTriggerInstances(std::vector<Node>& nodes);

  /** is instance of
   *
   * We say a term t is an trigger instance of term s if
   * (1) t = s * { x1 -> t1 ... xn -> tn }
   * (2) { x1, ..., xn } are a subset of FV( t ).
   * For example, f( g( h( x, x ) ) ) and f( g( x ) ) are instances of f( x ),
   * but f( g( y ) ) and g( x ) are not instances of f( x ).
   *
   * When this method returns -1, n1 is an instance of n2,
   * When this method returns 1, n1 is an instance of n2.
   *
   * The motivation for this method is to discard triggers s that are less
   * restrictive (criteria (1)) and serve to bind the same variables (criteria
   * (2)) as another trigger t. This often helps avoiding matching loops.
   */
  static int isTriggerInstanceOf(Node n1,
                                 Node n2,
                                 const std::vector<Node>& fv1,
                                 const std::vector<Node>& fv2);
  /** The quantified formula this trigger is for. */
  Node d_quant;
}; /* class Trigger */

}  // namespace inst
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__QUANTIFIERS__TRIGGER_H */

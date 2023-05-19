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
 * Pattern term selector class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__PATTERN_TERM_SELECTOR_H
#define CVC5__THEORY__QUANTIFIERS__PATTERN_TERM_SELECTOR_H

#include <map>

#include "expr/node.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/**
 * Pattern term selector, which is responsible for constructing a pool of terms,
 * generally based on the body of a quantified formula, which is then used for
 * selecting triggers.
 */
class PatternTermSelector
{
 public:
  /**
   * @param opts Reference to the options, which impacts pattern term selection
   * @param q The quantified formula we are selecting pattern terms for
   * @param tstrt the selection strategy (see options/quantifiers_mode.h),
   * @param exc The set of terms we are excluding as pattern terms.
   * @param filterInst when true, we discard terms that have instances
   * in the pattern terms we are return, e.g. we do not return f(x) if we are
   * also returning f(f(x)). This is default true since it helps in practice
   * to filter trigger instances.
   */
  PatternTermSelector(const Options& opts,
                      Node q,
                      options::TriggerSelMode tstrt,
                      const std::vector<Node>& exc = {},
                      bool filterInst = true);
  ~PatternTermSelector();
  /** collect pattern terms
   *
   * This collects all terms that are eligible for triggers for the quantified
   * formula of this class in term n and adds them to patTerms.
   *
   * @param n The node to collect pattern terms from
   * @param patTerm The vector to add pattern terms to
   * @param tinfo stores the result of the collection, mapping terms to the
   * information they are associated with.
   */
  void collect(Node n,
               std::vector<Node>& patTerms,
               std::map<Node, TriggerTermInfo>& tinfo);
  /** get is usable trigger
   *
   * Return the associated node of n that is a usable trigger in quantified
   * formula q. This may be different than n in several cases :
   * (1) Polarity information is explicitly converted to equalities, e.g.
   *      getIsUsableTrigger( (not (P x )), q ) may return (= (P x) false)
   * (2) Relational triggers are put into solved form, e.g.
   *      getIsUsableTrigger( (= (+ x a) 5), q ) may return (= x (- 5 a)).
   */
  static Node getIsUsableTrigger(const Options& opts, Node n, Node q);
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

  /**
   * get all variables that E-matching can instantiate from a subterm n in
   * quantified formula q.
   *
   * This returns the union of all free variables in usable triggers that are
   * subterms of n.
   */
  static void getTriggerVariables(const Options& opts,
                                  Node n,
                                  Node q,
                                  std::vector<Node>& tvars);

 protected:
  /** Is n a usable trigger in quantified formula q?
   *
   * A usable trigger is one that is matchable and contains free variables only
   * from q.
   */
  static bool isUsableTrigger(const Options& opts, Node n, Node q);
  /** Is n a usable atomic trigger?
   *
   * A usable atomic trigger is a term that is both a useable trigger and an
   * atomic trigger.
   */
  static bool isUsableAtomicTrigger(const Options& opts, Node n, Node q);
  /** is subterm of trigger usable (helper function for isUsableTrigger) */
  static bool isUsable(const Options& opts, Node n, Node q);
  /** returns an equality that is equivalent to the equality eq and
   * is a usable trigger for q if one exists, otherwise returns Node::null().
   */
  static Node getIsUsableEq(const Options& opts, Node q, Node eq);
  /** returns whether n1 == n2 is a usable (relational) trigger for q. */
  static bool isUsableEqTerms(const Options& opts, Node q, Node n1, Node n2);
  /** Helper for collect, with a fixed strategy for selection and filtering */
  void collectInternal(Node n,
                       std::vector<Node>& patTerms,
                       std::map<Node, TriggerTermInfo>& tinfo,
                       options::TriggerSelMode tstrt,
                       bool filterInst);
  /** recursive helper function for collectPatTerms
   *
   * This collects the usable trigger terms in the subterm n of the body of
   * quantified formula of this class.
   * @param visited cache of the trigger terms collected for each visited node,
   * @param tinfo cache of trigger term info for each visited node,
   * @param tstrat the selection strategy (see options/quantifiers_mode.h)
   * @param pol/hasPol the polarity of node n in q (see QuantPhaseReq
   * theory/quantifiers/quant_util.h)
   * @param epol/hasEPol the entailed polarity of node n in q (see
   * QuantPhaseReq theory/quantifiers/quant_util.h)
   * @param knowIsUsable whether we know that n is a usable trigger.
   *
   * We add the triggers we collected recursively in n into added.
   */
  void collectTermsInternal(Node n,
                            std::map<Node, std::vector<Node> >& visited,
                            std::map<Node, TriggerTermInfo>& tinfo,
                            options::TriggerSelMode tstrt,
                            std::vector<Node>& added,
                            bool pol,
                            bool hasPol,
                            bool epol,
                            bool hasEPol,
                            bool knowIsUsable = false);

  /** filter all nodes that have instances
   *
   * This is used during collectModelInfo to filter certain trigger terms,
   * stored in nodes. This updates nodes so that no pairs of distinct nodes
   * (i,j) is such that i is a trigger instance of j or vice versa (see below).
   */
  static void filterInstances(std::vector<Node>& nodes);

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
   *
   * Notice that n1 and n2 are in instantiation constant form.
   */
  static int isInstanceOf(Node n1,
                          Node n2,
                          const std::vector<Node>& fv1,
                          const std::vector<Node>& fv2);
  /** Reference to options */
  const Options& d_opts;
  /** The quantified formula this trigger is for. */
  Node d_quant;
  /** The trigger selection strategy */
  options::TriggerSelMode d_tstrt;
  /** The set of terms to exclude */
  std::vector<Node> d_excluded;
  /** Whether we are filtering instances */
  bool d_filterInst;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

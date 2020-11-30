/*********************                                                        */
/*! \file trigger.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TRIGGER_H
#define CVC4__THEORY__QUANTIFIERS__TRIGGER_H

#include <map>

#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "options/quantifiers_options.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst {

class IMGenerator;
class InstMatchGenerator;

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
* equivalence class of b, and P( y, z ) to P-applications not in the equivalence
* class of true, as such instances will always be entailed by the ground
* equalities and disequalities the current context. Entailed instances are
* typically not helpful, and are discarded in Instantiate::addInstantiation(...)
* unless the option --no-inst-no-entail is enabled. For more details, see page
* 10 of "Congruence Closure with Free Variables", Barbosa et al., TACAS 2017.
*
* This example is referenced for each of the functions below.
*/
class TriggerTermInfo {
 public:
  TriggerTermInfo() : d_reqPol(0), d_weight(0) {}
  ~TriggerTermInfo() {}
  /** The free variables in the node
  *
  * In the trigger term info for f( x ) in the above example, d_fv = { x }
  * In the trigger term info for g( y ) in the above example, d_fv = { y }
  * In the trigger term info for P( y, z ) in the above example, d_fv = { y, z }
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
  *   if d_reqPol = -1, then this trigger term must be matched to terms *not* in
  *                     the equivalence class of d_reqPolEq.
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

/** A collection of nodes representing a trigger.
*
* This class encapsulates all implementations of E-matching in CVC4.
* Its primary use is as a utility of the quantifiers module InstantiationEngine
* (see theory/quantifiers/ematching/instantiation_engine.h) which uses Trigger to make
* appropriate calls to Instantiate::addInstantiation(...)
* (see theory/instantiate.h) for the instantiate utility of the quantifiers
* engine (d_quantEngine) associated with this trigger.  These calls
* queue instantiation lemmas to the output channel of TheoryQuantifiers during
* a full effort check.
*
* Concretely, a Trigger* t is used in the following way during a full effort
* check. Assume that t is associated with quantified formula q (see field d_f).
* We call :
*
* // setup initial information
* t->resetInstantiationRound();
* // will produce instantiations based on matching with all terms
* t->reset( Node::null() );
* // add all instantiations based on E-matching with this trigger and the
* // current context
* t->addInstantiations();
*
* This will result in (a set of) calls to
* Instantiate::addInstantiation(q, m1)...Instantiate::addInstantiation(q, mn),
* where m1...mn are InstMatch objects. These calls add the corresponding
* instantiation lemma for (q,mi) on the output channel associated with
* d_quantEngine.
*
* The Trigger class is wrapper around an underlying IMGenerator class, which
* implements various forms of E-matching for its set of nodes (d_nodes), which
* is refered to in the literature as a "trigger". A trigger is a set of terms
* whose free variables are the bound variables of a quantified formula q,
* and that is used to guide instantiations for q (for example, see "Efficient
* E-Matching for SMT Solvers" by de Moura et al).
*
* For example of an instantiation lemma produced by E-matching :
*
* quantified formula : forall x. P( x )
*            trigger : P( x )
*     ground context : ~P( a )
*
* Then E-matching matches P( x ) and P( a ), resulting in the match { x -> a }
* which is used to generate the instantiation lemma :
*   (forall x. P( x )) => P( a )
*
* Terms that are provided as input to a Trigger class via mkTrigger
* should be in "instantiation constant form", see TermUtil::getInstConstantNode.
* Say we have quantified formula q whose AST is the Node
*   (FORALL
*     (BOUND_VAR_LIST x)
*     (NOT (P x))
*     (INST_PATTERN_LIST (INST_PATTERN (P x))))
* then TermUtil::getInstConstantNode( q, (P x) ) = (P IC) where
* IC = TermUtil::getInstantiationConstant( q, i ).
* Trigger expects as input (P IC) to represent the Trigger (P x). This form
* ensures that references to bound variables are unique to quantified formulas,
* which is required to ensure the correctness of instantiation lemmas we
* generate.
*
*/
class Trigger {
  friend class IMGenerator;

 public:
  virtual ~Trigger();
  /** get the generator associated with this trigger */
  IMGenerator* getGenerator() { return d_mg; }
  /** Reset instantiation round.
   *
  * Called once at beginning of an instantiation round.
  */
  void resetInstantiationRound();
  /** Reset the trigger.
   *
  * eqc is the equivalence class from which to match ground terms. If eqc is
  * Node::null(), then we match ground terms from all equivalence classes.
  */
  void reset( Node eqc );
  /** add all available instantiations, based on the current context
  *
  * This function makes the appropriate calls to d_qe->addInstantiation(...)
  * based on the current ground terms and equalities in the current context,
  * via queries to functions in d_qe. This calls the addInstantiations function
  * of the underlying match generator. It can be extended to
  * produce instantiations beyond what is produced by the match generator
  * (for example, see theory/quantifiers/ematching/ho_trigger.h).
  */
  virtual int addInstantiations();
  /** Return whether this is a multi-trigger. */
  bool isMultiTrigger() { return d_nodes.size()>1; }
  /** Get instantiation pattern list associated with this trigger.
   *
  * An instantiation pattern list is the node representation of a trigger, in
  * particular, it is the third argument of quantified formulas which have user
  * (! ... :pattern) attributes.
  */
  Node getInstPattern();
  /* A heuristic value indicating how active this generator is.
   *
  * This returns the number of ground terms for the match operators in terms
  * from d_nodes. This score is only used with the experimental option
  *   --trigger-active-sel.
  */
  int getActiveScore();
  /** print debug information for the trigger */
  void debugPrint(const char* c)
  {
    Trace(c) << "TRIGGER( ";
    for (int i = 0; i < (int)d_nodes.size(); i++)
    {
      if (i > 0)
      {
        Trace(c) << ", ";
      }
      Trace(c) << d_nodes[i];
    }
    Trace(c) << " )";
  }
  /** mkTrigger method
   *
   * This makes an instance of a trigger object.
   *  qe     : pointer to the quantifier engine;
   *  q      : the quantified formula we are making a trigger for
   *  nodes  : the nodes comprising the (multi-)trigger
   *  keepAll: don't remove unneeded patterns;
   *  trOption : policy for dealing with triggers that already exist
   *             (see below)
   *  use_n_vars : number of variables that should be bound by the trigger
   *               typically, the number of quantified variables in q.
   */
  enum{
    TR_MAKE_NEW,    //make new trigger even if it already may exist
    TR_GET_OLD,     //return a previous trigger if it had already been created
    TR_RETURN_NULL  //return null if a duplicate is found
  };
  static Trigger* mkTrigger(QuantifiersEngine* qe,
                            Node q,
                            std::vector<Node>& nodes,
                            bool keepAll = true,
                            int trOption = TR_MAKE_NEW,
                            unsigned use_n_vars = 0);
  /** single trigger version that calls the above function */
  static Trigger* mkTrigger(QuantifiersEngine* qe,
                            Node q,
                            Node n,
                            bool keepAll = true,
                            int trOption = TR_MAKE_NEW,
                            unsigned use_n_vars = 0);
  /** make trigger terms
   *
   * This takes a set of eligible trigger terms and stores a subset of them in
   * trNodes, such that :
   *   (1) the terms in trNodes contain at least n_vars of the quantified
   *       variables in quantified formula q, and
   *   (2) the set trNodes is minimal, i.e. removing one term from trNodes
   *       always violates (1).
   */
  static bool mkTriggerTerms(Node q,
                             std::vector<Node>& nodes,
                             unsigned n_vars,
                             std::vector<Node>& trNodes);
  /** collect pattern terms
   *
   * This collects all terms that are eligible for triggers for quantified
   * formula q in term n and adds them to patTerms.
   *   tstrt : the selection strategy (see options/quantifiers_mode.h),
   *   exclude :  a set of terms that *cannot* be selected as triggers,
   *   tinfo : stores the result of the collection, mapping terms to the
   *           information they are associated with,
   *   filterInst : flag that when true, we discard terms that have instances
   *     in the vector we are returning, e.g. we do not return f( x ) if we are
   *     also returning f( f( x ) ). TODO: revisit this (issue #1211)
   */
  static void collectPatTerms(Node q,
                              Node n,
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
  static bool isUsableTrigger( Node n, Node q );
  /** get is usable trigger
   *
   * Return the associated node of n that is a usable trigger in quantified
   * formula q. This may be different than n in several cases :
   * (1) Polarity information is explicitly converted to equalities, e.g.
   *      getIsUsableTrigger( (not (P x )), q ) may return (= (P x) false)
   * (2) Relational triggers are put into solved form, e.g.
   *      getIsUsableTrigger( (= (+ x a) 5), q ) may return (= x (- 5 a)).
   */
  static Node getIsUsableTrigger( Node n, Node q );
  /** Is n a usable atomic trigger?
   *
   * A usable atomic trigger is a term that is both a useable trigger and an
   * atomic trigger.
   */
  static bool isUsableAtomicTrigger( Node n, Node q );
  /** is n an atomic trigger?
  *
  * An atomic trigger is one whose kind is an atomic trigger kind.
  */
  static bool isAtomicTrigger( Node n );
  /** Is k an atomic trigger kind?
   *
  * An atomic trigger kind is one for which term indexing/matching is possible.
  */
  static bool isAtomicTriggerKind( Kind k );
  /** is n a relational trigger, e.g. like x >= a ? */
  static bool isRelationalTrigger( Node n );
  /** Is k a relational trigger kind? */
  static bool isRelationalTriggerKind( Kind k );
  /** is n a simple trigger (see inst_match_generator.h)? */
  static bool isSimpleTrigger( Node n );
  /** is n a pure theory trigger, e.g. head( x )? */
  static bool isPureTheoryTrigger( Node n );
  /** get trigger weight
   *
   * Intutively, this function classifies how difficult it is to handle the
   * trigger term n, where the smaller the value, the easier.
   *
   * Returns 0 for triggers that are APPLY_UF terms.
   * Returns 1 for other triggers whose kind is atomic.
   * Returns 2 otherwise.
   */
  static int getTriggerWeight( Node n );
  /** Returns whether n is a trigger term with a local theory extension
  * property from Bansal et al., CAV 2015.
  */
  static bool isLocalTheoryExt( Node n, std::vector< Node >& vars,
                                std::vector< Node >& patTerms );
  /** get the variable associated with an inversion for n
   *
   * A term n with an inversion variable x has the following property :
   *   There exists a closed function f such that for all terms t
   *   |= (n = t) <=> (x = f(t))
   * For example, getInversionVariable( x+1 ) returns x since for all terms t,
   *   |= x+1 = t <=> x = (\y. y-1)(t)
   * We call f the inversion function for n.
   */
  static Node getInversionVariable( Node n );
  /** Get the body of the inversion function for n whose argument is y.
   * e.g. getInversion( x+1, y ) returns y-1
   */
  static Node getInversion(Node n, Node y);
  /** get all variables that E-matching can instantiate from a subterm n.
   *
   * This returns the union of all free variables in usable triggers that are
   * subterms of n.
   */
  static void getTriggerVariables(Node n, Node f, std::vector<Node>& t_vars);

 protected:
  /** trigger constructor, intentionally protected (use Trigger::mkTrigger). */
  Trigger(QuantifiersEngine* ie, Node q, std::vector<Node>& nodes);
  /** is subterm of trigger usable (helper function for isUsableTrigger) */
  static bool isUsable( Node n, Node q );
  /** returns an equality that is equivalent to the equality eq and
  * is a usable trigger for q if one exists, otherwise returns Node::null().
  */
  static Node getIsUsableEq( Node q, Node eq );
  /** returns whether n1 == n2 is a usable (relational) trigger for q. */
  static bool isUsableEqTerms( Node q, Node n1, Node n2 );
  /** recursive helper function for collectPatTerms
   *
   * This collects the usable trigger terms in the subterm n of the body of
   * quantified formula q.
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
  static void collectPatTerms2(Node q,
                               Node n,
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
                                 std::vector<Node>& fv1,
                                 std::vector<Node>& fv2);

  /** add an instantiation (called by InstMatchGenerator)
   *
   * This calls Instantiate::addInstantiation(...) for instantiations
   * associated with m. Typically, m is associated with a single instantiation,
   * but in some cases (e.g. higher-order) we may modify m before calling
   * Instantiate::addInstantiation(...).
   */
  virtual bool sendInstantiation(InstMatch& m);
  /** The nodes comprising this trigger. */
  std::vector< Node > d_nodes;
  /** The quantifiers engine associated with this trigger. */
  QuantifiersEngine* d_quantEngine;
  /** The quantified formula this trigger is for. */
  Node d_quant;
  /** match generator
   *
  * This is the back-end utility that implements the underlying matching
  * algorithm associated with this trigger.
  */
  IMGenerator* d_mg;
}; /* class Trigger */

/** A trie of triggers.
*
* This class is used to cache all Trigger objects that are generated in the
* current context. We index Triggers in this data structure based on the
* value of Trigger::d_nodes. When a Trigger is added to this data structure,
* this Trie assumes responsibility for deleting it.
*/
class TriggerTrie {
public:
  TriggerTrie();
  ~TriggerTrie();
  /** get trigger
  * This returns a Trigger t that is indexed by nodes,
  * or NULL otherwise.
  */
  Trigger* getTrigger(std::vector<Node>& nodes);
  /** add trigger
  * This adds t to the trie, indexed by nodes.
  * In typical use cases, nodes is t->d_nodes.
  */
  void addTrigger(std::vector<Node>& nodes, Trigger* t);

 private:
  /** The trigger at this node in the trie. */
  std::vector<Trigger*> d_tr;
  /** The children of this node in the trie. */
  std::map< TNode, TriggerTrie* > d_children;
};/* class inst::Trigger::TriggerTrie */

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__TRIGGER_H */

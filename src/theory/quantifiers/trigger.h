/*********************                                                        */
/*! \file trigger.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief trigger class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TRIGGER_H
#define __CVC4__THEORY__QUANTIFIERS__TRIGGER_H

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
* Notice that it is only useful to match f( x ) to terms not in the equivalence class of b,
* and P( y, z ) to terms in the equivalence class of false, as such instances will always be 
* redundant/entailed in the current context.
*
* This example is referenced for each of the functions below.
*/
class TriggerTermInfo {
public:
  TriggerTermInfo() : d_reqPol(0){}
  ~TriggerTermInfo(){}
  /** The free variables in the node 
  *
  * For the trigger term info for f( x ) in the above example, d_fv = { x } 
  * For the trigger term info for g( y ) in the above example, d_fv = { y } 
  * For the trigger term info for P( y, z ) in the above example, d_fv = { y, z } 
  */
  std::vector< Node > d_fv;
  /** Required polarity:  1 for equality, -1 for disequality, 0 for none
  *
  * For the trigger term info for f( x ) in the above example, d_reqPol = -1
  * For the trigger term info for g( y ) in the above example, d_reqPol = 0 
  * For the trigger term info for P( y, z ) in the above example,  d_reqPol = 1
  */
  int d_reqPol;
  /** Required polarity equal term
  *
  * If d_reqPolEq is not null, 
  *   if d_reqPol = 1, then this trigger term must be matched to terms in the equivalence class of d_reqPolEq
  *   if d_reqPol = -1, then this trigger term must be matched to terms *not* in the equivalence class of d_reqPolEq
  *
  * This information is typically chosen by analyzing the entailed equalities and disequalities of quantified formulas.
  * For the trigger term info for f( x ) in the above example, d_reqPolEq = b
  * For the trigger term info for g( y ) in the above example, d_reqPolEq = Node::null()
  * For the trigger term info for P( y, z ) in the above example,  d_reqPolEq = false
  */
  Node d_reqPolEq;
  /** Initialize this information class (can be called more than once). 
  * q is the quantified formula that n is a trigger term for
  * n is the trigger term
  * reqPol/reqPolEq are described above
  */
  void init( Node q, Node n, int reqPol = 0, Node reqPolEq = Node::null() );
};

/** A collection of nodes representing a trigger. 
*
* This class encapsulates all implementations of E-matching in CVC4.
* Its primary use is as a utility of the quantifiers module InstantiationEngine (see theory/quantifiers/instantiation_engine.h)
* which uses Trigger to make appropriate calls to QuantifiersEngine::addInstantiation(...) (see theory/quantifiers_engine.h)
* for the quantifiers engine (d_quantEngine) associated with this trigger.  These calls
* queue instantiation lemmas to the output channel of TheoryQuantifiers during a full effort check.
*
* Concretely, a Trigger* t is used in the following way during a full effort check.
* Assume that t is associated with quantified formula q (see field d_f). We call :
*
* t->resetInstantiationRound();      // setup initial information
* t->reset( Node::null() );          // will produce instantiations based on matching with all terms
* InstMatch baseMatch;
* t->addInstantiations( baseMatch ); // add all instantiations based on E-matching with this trigger and the current context
*
* This will result in (a set of) calls to QuantifiersEngine::addInstantiation( q, m1 )...QuantifiersEngine::addInstantiation( q, mn ),
* where m1...mn are InstMatch objects. These calls add the corresponding instantiation lemma for (q,mi) on the output channel
* associated with d_quantEngine.
*
* The Trigger class is wrapper around an underlying IMGenerator class, which implements various forms 
* of E-matching for the set of nodes (d_nodes), which is refered to in the literature as a "trigger".
* A trigger is a set of terms whose free variables are the bound variables of a quantified formula q, 
* and that are used to guide instantiations for q (for example, see "Efficient E-Matching for SMT Solvers" by de Moura et al). 
*
* For example of an instantiation lemma produced by E-matching :
*
* quantified formula : forall x. P( x )
*            trigger : P( x )
*     ground context : ~P( a )
*
* Then E-matching matches P( x ) and P( a ), resulting in the match { x -> a } which is used to generate the instantiation lemma :
* (forall x. P( x )) => P( a )
*
* Terms that are provided as input to a Trigger class should be in "instantiation constant form", see TermUtil::getInstConstantNode.
* Say we have quantified formula q = (FORALL (BOUND_VAR_LIST x) (NOT (P x)) (INST_PATTERN_LIST (INST_PATTERN (P x)))),
* then TermUtil::getInstConstantNode( q, (P x) ) = (P i) where i = TermUtil::getInstantiationConstant( q, i ).
* Trigger expects as input (P i) to represent the Trigger (P x).
*/
class Trigger {
  friend class IMGenerator;
public:
  virtual ~Trigger();
  /** get the generator associated with this trigger */
  IMGenerator* getGenerator() { return d_mg; }
  /** Reset instantiation round. 
  * Called once at beginning of an instantiation round.
  */
  void resetInstantiationRound();
  /** Reset the trigger.
  * eqc is the equivalence class from which to match ground terms.
  * If eqc is Node::null(), then we match ground terms from all equivalence classes.
  */
  void reset( Node eqc );
  /** add all available instantiations, based on the current context
  *
  * This function makes the appropriate calls to d_qe->addInstantiation(...) based on the current
  * ground terms and equalities in the current context, via queries to functions in d_qe. This 
  * calls the addInstantiations function of the underlying match generator. It can be extended to
  * produce instantiations beyond what is produced by the match generator (for example, see theory/quantifiers/ho_trigger.h).
  *
  * baseMatch is a mapping of default values that should be used for variables that are not bound by this
  *   These default values are not frequently used in instantiations.
  */
  virtual int addInstantiations( InstMatch& baseMatch );
  /** Return whether this is a multi-trigger. */
  bool isMultiTrigger() { return d_nodes.size()>1; }
  /** Get instantiation pattern list associated with this trigger.
  * An instantiation pattern list in the node representation of a trigger, in particular, it
  * is the third argument of quantified formulas which have user (! ... :pattern) attributes.
  */
  Node getInstPattern();
  /* A heuristic value indicating how active this generator is. 
  * This returns the number of ground terms for the match operators in terms from d_nodes.
  * This score is only used with the experimental option --trigger-active-sel.
  */
  int getActiveScore();
  /** print debug information for the trigger */
  void debugPrint( const char * c ) {
    Trace(c) << "TRIGGER( ";
    for( int i=0; i<(int)d_nodes.size(); i++ ){
      if( i>0 ){ Trace(c) << ", "; }
      Trace(c) << d_nodes[i];
    }
    Trace(c) << " )";
  }
  /** mkTrigger method
  *  qe     : point to the quantifier engine;
  *  q      : the quantified formula we are making a trigger for
  *  nodes  : the nodes comprising the (multi-)trigger
  *  keepAll: don't remove unneeded patterns;
  *  trOption : policy for dealing with triggers that already exist
  *             (see below)
  *  use_n_vars : number of variables that should be bound by the trigger
  *               typically, the number of quantified variables in f.
  */
  enum{
    TR_MAKE_NEW,    //make new trigger even if it already may exist
    TR_GET_OLD,     //return a previous trigger if it had already been created
    TR_RETURN_NULL  //return null if a duplicate is found
  };
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node q, std::vector< Node >& nodes,
                             bool keepAll = true, int trOption = TR_MAKE_NEW, unsigned use_n_vars = 0 );
  /** single trigger version that calls the above function */
  static Trigger* mkTrigger( QuantifiersEngine* qe, Node q, Node n, bool keepAll = true,
                             int trOption = TR_MAKE_NEW, unsigned use_n_vars = 0 );
  /** make trigger terms 
  * This takes a set of eligible trigger terms and stores a subset of them in trNodes, such that :
  *   (1) the terms in trNodes contain at least n_vars of the quantified variables in quantified formula q, and
  *   (2) the set trNodes is minimal, i.e. removing one term from trNodes always violates (1).
  */
  static bool mkTriggerTerms( Node q, std::vector< Node >& nodes, unsigned n_vars, std::vector< Node >& trNodes );
  /** collectPatTerms
  * This collects all terms that are eligible for triggers for quantified formula q in term n.
  *   tstrt is the selection strategy
  *   exclude is a set of terms that *cannot* be selected as triggers 
  *   tinfo stores the result of the collection, mapping terms to information they are associated with
  *   filterInst is a flag that when true, we discard terms that have instances in the vector we are returning.
  *     e.g. we do not return f( x ) if we are also returning f( f( x ) ).
  *     TODO: revisit this (issue #1211)
  *
  * Trigger selection strategies are given by TriggerSelMode (see options/quantifiers_mode.h).
  */     
  static void collectPatTerms( Node q, Node n, std::vector< Node >& patTerms, quantifiers::TriggerSelMode tstrt,
                               std::vector< Node >& exclude, std::map< Node, TriggerTermInfo >& tinfo,
                               bool filterInst = false );
  /** Is n a usable trigger in quantified formula q? 
  * A usable trigger is one that is matchable and contains free variables only from q.
  */
  static bool isUsableTrigger( Node n, Node q );
  /** Return the associated node of n that is a usable trigger in quantified formula q.
  */
  static Node getIsUsableTrigger( Node n, Node q );
  /** Iis n a usable atomic trigger? 
  * A usable atomic trigger is a term that is both a useable trigger and an atomic trigger.
  */
  static bool isUsableAtomicTrigger( Node n, Node q );
  /** is n an atomic trigger? 
  * An atomic trigger is one whose kind is an atomic trigger kind.
  */
  static bool isAtomicTrigger( Node n );
  /** Is k an atomic trigger kind?
  * An atomic trigger kind is one for which term indexing/matching is possible. 
  */
  static bool isAtomicTriggerKind( Kind k );
  /** is n a relational trigger, e.g. like x >= a ? */
  static bool isRelationalTrigger( Node n );
  /** Is k a relational trigger kind? */
  static bool isRelationalTriggerKind( Kind k );
  /** Is k a kind for which counterexample-guided instantiation is possible? 
  * This typically corresponds to kinds that correspond to operators that
  * have a total interpretations and are a part of the signature of 
  * satisfaction complete theories (see Reynolds et al., CAV 2015).
  */
  static bool isCbqiKind( Kind k );
  /** is n a simple trigger (see inst_match_generator.h)? */
  static bool isSimpleTrigger( Node n );
  /** is n a Boolean term trigger, e.g. ite( x, BV1, BV0 )? */
  static bool isBooleanTermTrigger( Node n );
  /** is n a pure theory trigger, e.g. head( x )? */ 
  static bool isPureTheoryTrigger( Node n );
  /** get trigger weight
  * Returns 0 for triggers that are easy to process and 1 otherwise. 
  * A trigger is easy to process if it is an atomic trigger, or a relational trigger
  * of the form x ~ g.
  */
  static int getTriggerWeight( Node n );
  /** Returns whether n is a trigger term with a local theory extension
  * property from Bansal et al., CAV 2015.
  */
  static bool isLocalTheoryExt( Node n, std::vector< Node >& vars,
                                std::vector< Node >& patTerms );
  /** get the variable associated with an inversion for n
  * A term n with an inversion variable x has the following property :
  *   There exists a closed function f such that for all terms t
        |= (n = t) <=> (x = f(t))
  * For example, getInversionVariable( x+1 ) returns x since for all terms t,
  *   |= x+1 = t <=> x = (\y. y-1)(t)
  * We call f the inversion function for n.
  */
  static Node getInversionVariable( Node n );
  /** get the body of inversion function for n, e.g. getInversion( x+1, y ) returns y-1 */
  static Node getInversion( Node n, Node x );
  /** get all variables that E-matching can instantiate from a subterm n.
  * This returns the union of all free variables in usable triggers that are subterms of n.
  */
  static void getTriggerVariables( Node n, Node f, std::vector< Node >& t_vars );
protected:
  /** trigger constructor, intentionally protected (use Trigger::mkTrigger). */
  Trigger( QuantifiersEngine* ie, Node f, std::vector< Node >& nodes );
  /** is subterm of trigger usable (helper function for isUsableTrigger) */
  static bool isUsable( Node n, Node q );
  /** returns an equality that is equivalent to the equality eq and 
  * is a usable trigger for q if one exists, otherwise returns Node::null().
  */
  static Node getIsUsableEq( Node q, Node eq );
  /** returns whether n1 == n2 is a usable (relational) trigger for q. */
  static bool isUsableEqTerms( Node q, Node n1, Node n2 );
  /** helper function for collectPatTerms */
  static void collectPatTerms2( Node q, Node n, std::map< Node, std::vector< Node > >& visited, std::map< Node, TriggerTermInfo >& tinfo, 
                                quantifiers::TriggerSelMode tstrt, std::vector< Node >& exclude, std::vector< Node >& added,
                                bool pol, bool hasPol, bool epol, bool hasEPol, bool knowIsUsable = false );
                                
  /** add an instantiation (called by InstMatchGenerator) 
  * This calls d_quantEngine->addInstantiation(...) for instantiations associated with m.
  * Typically, m is associated with a single instantiation, but in some cases (e.g. higher-order)
  * we may modify m before sending it.
  */
  virtual bool sendInstantiation( InstMatch& m );
  /** The nodes comprising this trigger. */
  std::vector< Node > d_nodes;
  /** The quantifiers engine associated with this trigger. */
  QuantifiersEngine* d_quantEngine;
  /** The quantifier this trigger is for. */
  Node d_f;
  /** match generator
  * This is backend utility that implements the underlying matching algorithm
  * associated with this trigger.
  */
  IMGenerator* d_mg;
}; /* class Trigger */

/** A trie of triggers.
* 
* This class is used for caching Trigger objects.
* We store Triggers in this data structure based on Trigger::d_nodes.
*/
class TriggerTrie {
public:
  TriggerTrie();
  ~TriggerTrie();
  /** Lookup a trigger for a vector of nodes. 
  * This returns a Trigger t such that t->d_nodes = nodes if one exists, 
  * or NULL otherwise.
  */
  inst::Trigger* getTrigger( std::vector< Node >& nodes ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return getTrigger2( temp );
  }
  /** Add trigger to trie.
  * It should be the case that t->d_nodes = nodes.
  */
  void addTrigger( std::vector< Node >& nodes, inst::Trigger* t ){
    std::vector< Node > temp;
    temp.insert( temp.begin(), nodes.begin(), nodes.end() );
    std::sort( temp.begin(), temp.end() );
    return addTrigger2( temp, t );
  }
private:
  /** Helper function for getTrigger */
  inst::Trigger* getTrigger2( std::vector< Node >& nodes );
  /** Helper function for addTrigger */
  void addTrigger2( std::vector< Node >& nodes, inst::Trigger* t );
  /** The trigger at this node in the trie. */
  std::vector< inst::Trigger* > d_tr;
  /** The children of this node in the trie. */
  std::map< TNode, TriggerTrie* > d_children;
};/* class inst::Trigger::TriggerTrie */

}/* CVC4::theory::inst namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TRIGGER_H */

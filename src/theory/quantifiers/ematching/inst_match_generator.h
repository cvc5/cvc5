/*********************                                                        */
/*! \file inst_match_generator.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief inst match generator class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H
#define __CVC4__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H

#include <map>
#include "theory/quantifiers/inst_match_trie.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
namespace quantifiers{
  class TermArgTrie;
}

namespace inst {

class Trigger;

/** IMGenerator class
*
* Virtual base class for generating InstMatch objects, which correspond to
* quantifier instantiations. The main use of this class is as a backend utility
* to Trigger (see theory/quantifiers/trigger.h).
*
* Some functions below take as argument a pointer to the current quantifiers
* engine, which is used for making various queries about what terms and
* equalities exist in the current context.
*
* Some functions below take a pointer to a parent Trigger object, which is used
* to post-process and finalize the instantiations through
* sendInstantiation(...), where the parent trigger will make calls to
* qe->getInstantiate()->addInstantiation(...). The latter function is the entry
* point in which instantiate lemmas are enqueued to be sent on the output
* channel.
*/
class IMGenerator {
public:
  virtual ~IMGenerator() {}
  /** Reset instantiation round.
  *
  * Called once at beginning of an instantiation round.
  */
  virtual void resetInstantiationRound(QuantifiersEngine* qe) {}
  /** Reset.
  *
  * eqc is the equivalence class to search in (any if eqc=null).
  * Returns true if this generator can produce instantiations, and false
  * otherwise. An example of when it returns false is if it can be determined
  * that no appropriate matchable terms occur based on eqc.
  */
  virtual bool reset(Node eqc, QuantifiersEngine* qe) { return true; }
  /** Get the next match.
  *
  * Must call reset( eqc ) before this function. This constructs an
  * instantiation, which it populates in data structure m,
  * based on the current context using the implemented matching algorithm.
  *
  * q is the quantified formula we are adding instantiations for
  * m is the InstMatch object we are generating
  *
  * Returns a value >0 if an instantiation was successfully generated
  */
  virtual int getNextMatch(Node q,
                           InstMatch& m,
                           QuantifiersEngine* qe,
                           Trigger* tparent)
  {
    return 0;
  }
  /** add instantiations
  *
  * This add all available instantiations for q based on the current context
  * using the implemented matching algorithm. It typically is implemented as a
  * fixed point of getNextMatch above.
  *
  * It returns the number of instantiations added using calls to calls to
  * Instantiate::addInstantiation(...).
  */
  virtual int addInstantiations(Node q,
                                QuantifiersEngine* qe,
                                Trigger* tparent)
  {
    return 0;
  }
  /** get active score
  *
  * A heuristic value indicating how active this generator is.
  */
  virtual int getActiveScore( QuantifiersEngine * qe ) { return 0; }
 protected:
  /** send instantiation
   *
   * This method sends instantiation, specified by m, to the parent trigger
   * object, which will in turn make a call to
   * Instantiate::addInstantiation(...). This method returns true if a
   * call to Instantiate::addInstantiation(...) was successfully made,
   * indicating that an instantiation was enqueued in the quantifier engine's
   * lemma cache.
   */
  bool sendInstantiation(Trigger* tparent, InstMatch& m);
};/* class IMGenerator */

class CandidateGenerator;

/** InstMatchGenerator class
*
* This is the default generator class for non-simple single triggers, that is,
* triggers composed of a single term with nested term applications.
* For example, { f( y, f( x, a ) ) } and { f( g( x ), a ) } are non-simple
* triggers.
*
* Handling non-simple triggers is done by constructing a linked list of
* InstMatchGenerator classes (see mkInstMatchGenerator), where each
* InstMatchGenerator has a "d_next" pointer.  If d_next is NULL,
* then this is the end of the InstMatchGenerator and the last
* InstMatchGenerator is responsible for finalizing the instantiation.
*
* For (EX1), for the trigger f( y, f( x, a ) ), we construct the linked list:
*
* [ f( y, f( x, a ) ) ] -> [ f( x, a ) ] -> NULL
*
* In a call to getNextMatch,
* if we match against a ground term f( b, c ), then the first InstMatchGenerator
* in this list binds y to b, and tells the InstMatchGenerator [ f( x, a ) ] to
* match f-applications in the equivalence class of c.
*
* CVC4 employs techniques that ensure that the number of instantiations
* is worst-case polynomial wrt the number of ground terms.
* Consider the axiom/pattern/context (EX2) :
*
*          axiom : forall x1 x2 x3 x4. F[ x1...x4 ]
*
*        trigger : P( f( x1 ), f( x2 ), f( x3 ), f( x4 ) )
*
* ground context : ~P( a, a, a, a ), a = f( c_1 ) = ... = f( c_100 )
*
* If E-matching were applied exhaustively, then x1, x2, x3, x4 would be
* instantiated with all combinations of c_1, ... c_100, giving 100^4
* instantiations.
*
* Instead, we enforce that at most 1 instantiation is produced for a
* ( pattern, ground term ) pair per round. Meaning, only one instantiation is
* generated when matching P( a, a, a, a ) against the generator
* [P( f( x1 ), f( x2 ), f( x3 ), f( x4 ) )]. For details, see Section 3 of
* Reynolds, Vampire 2016.
*
* To enforce these policies, we use a flag "d_active_add" which dictates the
* behavior of the last element in the linked list. If d_active_add is
*   true -> a call to getNextMatch(...) returns 1 only if adding the
*           instantiation via a call to IMGenerator::sendInstantiation(...)
*           successfully enqueues a lemma via a call to
*           Instantiate::addInstantiation(...). This call may fail e.g. if we
*           have already added the instantiation, or the instantiation is
*           entailed.
*   false -> a call to getNextMatch(...) returns 1 whenever an m is
*            constructed, where typically the caller would use m.
* This is important since a return value >0 signals that the current matched
* terms should be flushed. Consider the above example (EX1), where
* [ f(y,f(x,a)) ] is being matched against f(b,c),
* [ f(x,a) ] is being matched against f(d,a) where c=f(d,a)
* A successfully added instantiation { x->d, y->b } here signals we should
* not produce further instantiations that match f(y,f(x,a)) with f(b,c).
*
* A number of special cases of triggers are covered by this generator (see
* implementation of initialize), including :
*   Literal triggers, e.g. x >= a, ~x = y
*   Selector triggers, e.g. head( x )
*   Triggers with invertible subterms, e.g. f( x+1 )
*   Variable triggers, e.g. x
*
* All triggers above can be in the context of an equality, e.g.
* { f( y, f( x, a ) ) = b } is a trigger that matches f( y, f( x, a ) ) to
* ground terms in the equivalence class of b.
* { ~f( y, f( x, a ) ) = b } is a trigger that matches f( y, f( x, a ) ) to any
* ground terms not in the equivalence class of b.
*/
class InstMatchGenerator : public IMGenerator {
 public:
  /** destructor */
  ~InstMatchGenerator() override;

  /** Reset instantiation round. */
  void resetInstantiationRound(QuantifiersEngine* qe) override;
  /** Reset. */
  bool reset(Node eqc, QuantifiersEngine* qe) override;
  /** Get the next match. */
  int getNextMatch(Node q,
                   InstMatch& m,
                   QuantifiersEngine* qe,
                   Trigger* tparent) override;
  /** Add instantiations. */
  int addInstantiations(Node q,
                        QuantifiersEngine* qe,
                        Trigger* tparent) override;

  /** set active add flag (true by default)
   *
  * If active add is true, we call sendInstantiation in calls to getNextMatch,
  * instead of returning the match. This is necessary so that we can ensure
  * policies that are dependent upon knowing when instantiations are
  * successfully added to the output channel through
  * Instantiate::addInstantiation(...).
  */
  void setActiveAdd(bool val);
  /** Get active score for this inst match generator
   *
   * See Trigger::getActiveScore for details.
   */
  int getActiveScore(QuantifiersEngine* qe) override;
  /** exclude match
   *
   * Exclude matching d_match_pattern with Node n on subsequent calls to
   * getNextMatch.
   */
  void excludeMatch(Node n) { d_curr_exclude_match[n] = true; }
  /** Get current match.
   * Returns the term we are currently matching.
   */
  Node getCurrentMatch() { return d_curr_matched; }
  /** set that this match generator is independent
   *
  * A match generator is indepndent when this generator fails to produce a
  * match in a call to getNextMatch, the overall matching fails.
  */
  void setIndependent() { d_independent_gen = true; }
  //-------------------------------construction of inst match generators
  /** mkInstMatchGenerator for single triggers, calls the method below */
  static InstMatchGenerator* mkInstMatchGenerator(Node q,
                                                  Node pat,
                                                  QuantifiersEngine* qe);
  /** mkInstMatchGenerator for the multi trigger case
  *
  * This linked list of InstMatchGenerator classes with one
  * InstMatchGeneratorMultiLinear at the head and a list of trailing
  * InstMatchGenerators corresponding to each unique subterm of pats with
  * free variables.
  */
  static InstMatchGenerator* mkInstMatchGeneratorMulti(Node q,
                                                       std::vector<Node>& pats,
                                                       QuantifiersEngine* qe);
  /** mkInstMatchGenerator
  *
  * This generates a linked list of InstMatchGenerators for each unique
  * subterm of pats with free variables.
  *
  * q is the quantified formula associated with the generator we are making
  * pats is a set of terms we are making InstMatchGenerator nodes for
  * qe is a pointer to the quantifiers engine (used for querying necessary
  * information during initialization) pat_map_init maps from terms to
  * generators we have already made for them.
  *
  * It calls initialize(...) for all InstMatchGenerators generated by this call.
  */
  static InstMatchGenerator* mkInstMatchGenerator(
      Node q,
      std::vector<Node>& pats,
      QuantifiersEngine* qe,
      std::map<Node, InstMatchGenerator*>& pat_map_init);
  //-------------------------------end construction of inst match generators

 protected:
  /** constructors
   *
  * These are intentionally private, and are called during linked list
  * construction in mkInstMatchGenerator.
  */
  InstMatchGenerator(Node pat);
  InstMatchGenerator();
  /** The pattern we are producing matches for.
   *
  * This term and d_match_pattern can be different since this
  * term may involve  information regarding phase and (dis)equality entailment,
  * or other special cases of Triggers.
  *
  * For example, for the trigger for P( x ) = false, which matches P( x ) with
  * P( t ) in the equivalence class of false,
  *   P( x ) = false is d_pattern
  *   P( x ) is d_match_pattern
  * Another example, for pure theory triggers like head( x ), we have
  *   head( x ) is d_pattern
  *   x is d_match_pattern
  * since head( x ) can match any (List) datatype term x.
  *
  * If null, this is a multi trigger that is merging matches from d_children,
  * which is used in InstMatchGeneratorMulti.
  */
  Node d_pattern;
  /** The match pattern
   * This is the term that is matched against ground terms,
   * see examples above.
   */
  Node d_match_pattern;
  /** The current term we are matching. */
  Node d_curr_matched;
  /** do we need to call reset on this generator? */
  bool d_needsReset;
  /** candidate generator
   * This is the back-end utility for InstMatchGenerator.
   * It generates a stream of candidate terms to match against d_match_pattern
   * below, dependending upon what kind of term we are matching
   * (e.g. a matchable term, a variable, a relation, etc.).
   */
  CandidateGenerator* d_cg;
  /** children generators
   * These match generators correspond to the children of the term
   * we are matching with this generator.
   * For example [ f( x, a ) ] is a child of [ f( y, f( x, a ) ) ]
   * in the example (EX1) above.
   */
  std::vector<InstMatchGenerator*> d_children;
  /** for each child, the index in the term
   * For example [ f( x, a ) ] has index 1 in [ f( y, f( x, a ) ) ]
   * in the example (EX1) above, indicating it is the 2nd child
   * of the term.
   */
  std::vector<int> d_children_index;
  /** children types
   *
   * If d_match_pattern is an instantiation constant, then this is a singleton
   * vector containing the variable number of the d_match_pattern itself.
   * If d_match_patterm is a term of the form f( t1, ..., tn ), then for each
   * index i, d_children[i] stores the type of node ti is, where:
   *   >= 0 : variable (indicates its number),
   *   -1 : ground term,
   *   -2 : child term.
   */
  std::vector<int> d_children_types;
  /** The next generator in the linked list
   * that this generator is a part of.
   */
  InstMatchGenerator* d_next;
  /** The equivalence class we are currently matching in. */
  Node d_eq_class;
  /** If non-null, then this is a relational trigger of the form x ~
   * d_eq_class_rel. */
  Node d_eq_class_rel;
  /** Excluded matches
  * Stores the terms we are not allowed to match.
  * These can for instance be specified by the smt2
  * extended syntax (! ... :no-pattern).
  */
  std::map<Node, bool> d_curr_exclude_match;
  /** Current first candidate
  * Used in a key fail-quickly optimization which generates
  * the first candidate term to match during reset().
  */
  Node d_curr_first_candidate;
  /** Indepdendent generate
  * If this flag is true, failures to match should be cached.
  */
  bool d_independent_gen;
  /** active add flag, described above. */
  bool d_active_add;
  /** cached value of d_match_pattern.getType() */
  TypeNode d_match_pattern_type;
  /** the match operator for d_match_pattern
   *
   * See TermDatabase::getMatchOperator for details on match operators.
   */
  Node d_match_pattern_op;
  /** get the match against ground term or formula t.
   *
   * d_match_pattern and t should have the same shape, that is,
   * their match operator (see TermDatabase::getMatchOperator) is the same.
   * only valid for use where !d_match_pattern.isNull().
   */
  int getMatch(
      Node q, Node t, InstMatch& m, QuantifiersEngine* qe, Trigger* tparent);
  /** Initialize this generator.
   *
   * q is the quantified formula associated with this generator.
   *
   * This constructs the appropriate information about what
   * patterns we are matching and children generators.
   *
   * It may construct new (child) generators needed to implement
   * the matching algorithm for this term. For each new generator
   * constructed in this way, it adds them to gens.
   */
  void initialize(Node q,
                  QuantifiersEngine* qe,
                  std::vector<InstMatchGenerator*>& gens);
  /** Continue next match
   *
  * This is called during getNextMatch when the current generator in the linked
  * list succesfully satisfies its matching constraint. This function either
  * calls getNextMatch of the next element in the linked list, or finalizes the
  * match (calling sendInstantiation(...) if active add is true, or returning a
  * value >0 if active add is false).  Its return value has the same semantics
  * as getNextMatch.
  */
  int continueNextMatch(Node q,
                        InstMatch& m,
                        QuantifiersEngine* qe,
                        Trigger* tparent);
  /** Get inst match generator
   *
   * Gets the InstMatchGenerator that implements the
   * appropriate matching algorithm for n within q
   * within a linked list of InstMatchGenerators.
   */
  static InstMatchGenerator* getInstMatchGenerator(Node q, Node n);
};/* class InstMatchGenerator */

/** match generator for Boolean term ITEs
* This handles the special case of triggers that look like ite( x, BV1, BV0 ).
*/
class VarMatchGeneratorBooleanTerm : public InstMatchGenerator {
public:
  VarMatchGeneratorBooleanTerm( Node var, Node comp );

  /** Reset */
  bool reset(Node eqc, QuantifiersEngine* qe) override
  {
    d_eq_class = eqc; 
    return true;
  }
  /** Get the next match. */
  int getNextMatch(Node q,
                   InstMatch& m,
                   QuantifiersEngine* qe,
                   Trigger* tparent) override;

 private:
  /** stores the true branch of the Boolean ITE */
  Node d_comp;
  /** stores whether we have written a value for var in the current match. */
  bool d_rm_prev;
};

/** match generator for purified terms
* This handles the special case of invertible terms like x+1 (see
* Trigger::getTermInversionVariable).
*/
class VarMatchGeneratorTermSubs : public InstMatchGenerator {
public:
  VarMatchGeneratorTermSubs( Node var, Node subs );

  /** Reset */
  bool reset(Node eqc, QuantifiersEngine* qe) override
  {
    d_eq_class = eqc;
    return true;
  }
  /** Get the next match. */
  int getNextMatch(Node q,
                   InstMatch& m,
                   QuantifiersEngine* qe,
                   Trigger* tparent) override;

 private:
  /** variable we are matching (x in the example x+1). */
  TNode d_var;
  /** cache of d_var.getType() */
  TypeNode d_var_type;
  /** The substitution for what we match (x-1 in the example x+1). */
  Node d_subs;
  /** stores whether we have written a value for d_var in the current match. */
  bool d_rm_prev;
};

/** InstMatchGeneratorMultiLinear class
*
* This is the default implementation of multi-triggers.
*
* Handling multi-triggers using this class is done by constructing a linked
* list of InstMatchGenerator classes (see mkInstMatchGeneratorMulti), with one
* InstMatchGeneratorMultiLinear at the head and a list of trailing
* InstMatchGenerators.
*
* CVC4 employs techniques that ensure that the number of instantiations
* is worst-case polynomial wrt the number of ground terms, where this class
* lifts this policy to multi-triggers. In particular consider
*
*  multi-trigger : { f( x1 ), f( x2 ), f( x3 ), f( x4 ) }
*
* For this multi-trigger, we insist that for each i=1...4, and each ground term
* t, there is at most 1 instantiation added as a result of matching
*    ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) )
* against ground terms of the form
*    ( s_1, s_2, s_3, s_4 ) where t = s_i for i=1,...,4.
* Meaning we add instantiations for the multi-trigger
* ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ) based on matching pairwise against:
*   ( f( c_i11 ), f( c_i21 ), f( c_i31 ), f( c_i41 ) )
*   ( f( c_i12 ), f( c_i22 ), f( c_i32 ), f( c_i42 ) )
*   ( f( c_i13 ), f( c_i23 ), f( c_i33 ), f( c_i43 ) )
* Where we require c_i{jk} != c_i{jl} for each i=1...4, k != l.
*
* For example, we disallow adding instantiations based on matching against both
* ( f( c_1 ), f( c_2 ), f( c_4 ), f( c_6 ) ) and
* ( f( c_1 ), f( c_3 ), f( c_5 ), f( c_7 ) )
* against ( f( x1 ), f( x2 ), f( x3 ), f( x4 ) ), since f( c_1 ) is matched
* against f( x1 ) twice.
*
* This policy can be disabled by --no-multi-trigger-linear.
*
*/
class InstMatchGeneratorMultiLinear : public InstMatchGenerator {
  friend class InstMatchGenerator;

 public:
  /** Reset. */
  bool reset(Node eqc, QuantifiersEngine* qe) override;
  /** Get the next match. */
  int getNextMatch(Node q,
                   InstMatch& m,
                   QuantifiersEngine* qe,
                   Trigger* tparent) override;

 protected:
  /** reset the children of this generator */
  int resetChildren(QuantifiersEngine* qe);
  /** constructor */
  InstMatchGeneratorMultiLinear(Node q,
                                std::vector<Node>& pats,
                                QuantifiersEngine* qe);
};/* class InstMatchGeneratorMulti */

/** InstMatchGeneratorMulti
*
* This is an earlier implementation of multi-triggers
* that is enabled by --multi-trigger-cache.
* This generator takes the product of instantiations
* found by single trigger matching, and does
* not have the guarantee that the number of
* instantiations is polynomial wrt the number of
* ground terms.
*/
class InstMatchGeneratorMulti : public IMGenerator {
 public:
  /** constructors */
  InstMatchGeneratorMulti(Node q,
                          std::vector<Node>& pats,
                          QuantifiersEngine* qe);
  /** destructor */
  ~InstMatchGeneratorMulti() override;

  /** Reset instantiation round. */
  void resetInstantiationRound(QuantifiersEngine* qe) override;
  /** Reset. */
  bool reset(Node eqc, QuantifiersEngine* qe) override;
  /** Add instantiations. */
  int addInstantiations(Node q,
                        QuantifiersEngine* qe,
                        Trigger* tparent) override;

 private:
  /** indexed trie */
  typedef std::pair< std::pair< int, int >, InstMatchTrie* > IndexedTrie;
  /** process new match
   *
   * Called during addInstantiations(...).
   * Indicates we produced a match m for child fromChildIndex
   * addedLemmas is how many instantiations we succesfully send
   * via IMGenerator::sendInstantiation(...) calls.
   */
  void processNewMatch(QuantifiersEngine* qe,
                       Trigger* tparent,
                       InstMatch& m,
                       int fromChildIndex,
                       int& addedLemmas);
  /** helper for process new match
   * tr is the inst match trie (term index) we are currently traversing.
   * trieIndex is depth we are in trie tr.
   * childIndex is the index of the term in the multi trigger we are currently
   *               processing.
   * endChildIndex is the index of the term in the multi trigger that generated
   *                  a new term, and hence we will end when the product
   *                  computed by this function returns to.
   * modEq is whether we are matching modulo equality.
   */
  void processNewInstantiations(QuantifiersEngine* qe,
                                Trigger* tparent,
                                InstMatch& m,
                                int& addedLemmas,
                                InstMatchTrie* tr,
                                int trieIndex,
                                int childIndex,
                                int endChildIndex,
                                bool modEq);
  /** Map from pattern nodes to indices of variables they contain. */
  std::map< Node, std::vector< int > > d_var_contains;
  /** Map from variable indices to pattern nodes that contain them. */
  std::map< int, std::vector< Node > > d_var_to_node;
  /** quantified formula we are producing matches for */
  Node d_quant;
  /** children generators
   * These are inst match generators for each term in the multi trigger.
   */
  std::vector< InstMatchGenerator* > d_children;
  /** variable orderings
   * Stores a heuristically determined variable ordering (unique
   * variables first) for each term in the multi trigger.
   */
  std::map< unsigned, InstMatchTrie::ImtIndexOrder* > d_imtio;
  /** inst match tries for each child node
   * This data structure stores all InstMatch objects generated
   * by matching for each term in the multi trigger.
   */
  std::vector< InstMatchTrieOrdered > d_children_trie;
};/* class InstMatchGeneratorMulti */

/** InstMatchGeneratorSimple class
*
* This is the default generator class for simple single triggers.
* For example, { f( x, a ) }, { f( x, x ) } and { f( x, y ) } are simple single
* triggers. In practice, around 70-90% of triggers are simple single triggers.
*
* Notice that simple triggers also can have an attached polarity.
* For example, { P( x ) = false }, { f( x, y ) = a } and { ~f( a, x ) = b } are
* simple single triggers.
*
* The implementation traverses the term indices in TermDatabase for adding
* instantiations, which is more efficient than the techniques required for
* handling non-simple single triggers.
*
* In contrast to other instantiation generators, it does not call
* IMGenerator::sendInstantiation and for performance reasons instead calls
* qe->getInstantiate()->addInstantiation(...) directly.
*/
class InstMatchGeneratorSimple : public IMGenerator {
 public:
  /** constructors */
  InstMatchGeneratorSimple(Node q, Node pat, QuantifiersEngine* qe);

  /** Reset instantiation round. */
  void resetInstantiationRound(QuantifiersEngine* qe) override;
  /** Add instantiations. */
  int addInstantiations(Node q,
                        QuantifiersEngine* qe,
                        Trigger* tparent) override;
  /** Get active score. */
  int getActiveScore(QuantifiersEngine* qe) override;

 private:
  /** quantified formula for the trigger term */
  Node d_quant;
  /** the trigger term */
  Node d_match_pattern;
  /** equivalence class polarity information
   *
  * This stores the required polarity/equivalence class with this trigger.
  * If d_eqc is non-null, we only produce matches { x->t } such that
  * our context does not entail
  *   ( d_match_pattern*{ x->t } = d_eqc) if d_pol = true, or
  *   ( d_match_pattern*{ x->t } != d_eqc) if d_pol = false.
  * where * denotes application of substitution.
  */
  bool d_pol;
  Node d_eqc;
  /** Match pattern arg types.
   * Cached values of d_match_pattern[i].getType().
   */
  std::vector< TypeNode > d_match_pattern_arg_types;
  /** The match operator d_match_pattern (see TermDb::getMatchOperator). */
  Node d_op;
  /** Map from child number to variable index. */
  std::map< int, int > d_var_num;
  /** add instantiations, helper function.
   *
   * m is the current match we are building,
   * addedLemmas is the number of lemmas we have added via calls to
   *                qe->getInstantiate()->aaddInstantiation(...),
   * argIndex is the argument index in d_match_pattern we are currently
   *              matching,
   * tat is the term index we are currently traversing.
   */
  void addInstantiations(InstMatch& m,
                         QuantifiersEngine* qe,
                         int& addedLemmas,
                         unsigned argIndex,
                         quantifiers::TermArgTrie* tat);
};/* class InstMatchGeneratorSimple */
}
}
}

#endif

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Inst match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_H

#include <map>
#include "expr/node.h"
#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/ematching/im_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

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
 * if we match against a ground term f( b, c ), then the first
 * InstMatchGenerator in this list binds y to b, and tells the
 * InstMatchGenerator [ f( x, a ) ] to match f-applications in the equivalence
 * class of c.
 *
 * cvc5 employs techniques that ensure that the number of instantiations
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
  void resetInstantiationRound() override;
  /** Reset. */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;
  /** Add instantiations. */
  uint64_t addInstantiations(InstMatch& m) override;

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
  int getActiveScore() override;
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
  static InstMatchGenerator* mkInstMatchGenerator(Env& env,
                                                  Trigger* tparent,
                                                  Node q,
                                                  Node pat);
  /** mkInstMatchGenerator for the multi trigger case
  *
  * This linked list of InstMatchGenerator classes with one
  * InstMatchGeneratorMultiLinear at the head and a list of trailing
  * InstMatchGenerators corresponding to each unique subterm of pats with
  * free variables.
  */
  static InstMatchGenerator* mkInstMatchGeneratorMulti(Env& env,
                                                       Trigger* tparent,
                                                       Node q,
                                                       std::vector<Node>& pats);
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
      Env& env,
      Trigger* tparent,
      Node q,
      std::vector<Node>& pats,
      std::map<Node, InstMatchGenerator*>& pat_map_init);
  //-------------------------------end construction of inst match generators

 protected:
  /** constructors
   *
  * These are intentionally private, and are called during linked list
  * construction in mkInstMatchGenerator.
  */
  InstMatchGenerator(Env& env, Trigger* tparent, Node pat);
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
  std::vector<size_t> d_children_index;
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
  std::vector<int64_t> d_children_types;
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
  int getMatch(Node t, InstMatch& m);
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
  int continueNextMatch(InstMatch& m, InferenceId id);
  /** Get inst match generator
   *
   * Gets the InstMatchGenerator that implements the
   * appropriate matching algorithm for n within q
   * within a linked list of InstMatchGenerators.
   */
  static InstMatchGenerator* getInstMatchGenerator(Env& env,
                                                   Trigger* tparent,
                                                   Node q,
                                                   Node n);
};/* class InstMatchGenerator */

}  // namespace inst
}
}
}  // namespace cvc5::internal

#endif

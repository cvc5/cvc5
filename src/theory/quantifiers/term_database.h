/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include <map>
#include <unordered_set>

#include "expr/attribute.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst{
  class Trigger;
  class HigherOrderTrigger;
}

namespace quantifiers {

namespace fmcheck {
  class FullModelChecker;
}

class TermDbSygus;
class QuantConflictFind;
class RelevantDomain;
class ConjectureGenerator;
class TermGenerator;
class TermGenEnv;

/** Term Database
 *
 * This class is a key utility used by
 * a number of approaches for quantifier instantiation,
 * including E-matching, conflict-based instantiation,
 * and model-based instantiation.
 *
 * The primary responsibilities for this class are to :
 * (1) Maintain a list of all ground terms that exist in the quantifier-free
 *     solvers, as notified through the master equality engine.
 * (2) Build TNodeTrie objects that index all ground terms, per operator.
 *
 * Like other utilities, its reset(...) function is called
 * at the beginning of full or last call effort checks.
 * This initializes the database for the round. However,
 * notice that TNodeTrie objects are computed
 * lazily for performance reasons.
 */
class TermDb : public QuantifiersUtil {
  friend class ::CVC4::theory::QuantifiersEngine;
  // TODO: eliminate these
  friend class ::CVC4::theory::quantifiers::ConjectureGenerator;
  friend class ::CVC4::theory::quantifiers::TermGenEnv;
  typedef context::CDHashMap<Node, int, NodeHashFunction> NodeIntMap;
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;

 public:
  TermDb(context::Context* c, context::UserContext* u, QuantifiersEngine* qe);
  ~TermDb();
  /** presolve (called once per user check-sat) */
  void presolve();
  /** reset (calculate which terms are active) */
  bool reset(Theory::Effort effort) override;
  /** register quantified formula */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "TermDb"; }
  /** get number of operators */
  unsigned getNumOperators();
  /** get operator at index i */
  Node getOperator(unsigned i);
  /** ground terms for operator
  * Get the number of ground terms with operator f that have been added to the
  * database
  */
  unsigned getNumGroundTerms(Node f) const;
  /** get ground term for operator
  * Get the i^th ground term with operator f that has been added to the database
  */
  Node getGroundTerm(Node f, unsigned i) const;
  /** get num type terms
  * Get the number of ground terms of tn that have been added to the database
  */
  unsigned getNumTypeGroundTerms(TypeNode tn) const;
  /** get type ground term
  * Returns the i^th ground term of type tn
  */
  Node getTypeGroundTerm(TypeNode tn, unsigned i) const;
  /** get or make ground term
   *
   * Returns the first ground term of type tn, or makes one if none exist. If
   * reqVar is true, then the ground term must be a variable.
   */
  Node getOrMakeTypeGroundTerm(TypeNode tn, bool reqVar = false);
  /** make fresh variable
  * Returns a fresh variable of type tn.
  * This will return only a single fresh
  * variable per type.
  */
  Node getOrMakeTypeFreshVariable(TypeNode tn);
  /** add a term to the database
  * withinQuant is whether n is within the body of a quantified formula
  * withinInstClosure is whether n is within an inst-closure operator (see
  * Bansal et al CAV 2015).
  */
  void addTerm(Node n,
               std::set<Node>& added,
               bool withinQuant = false,
               bool withinInstClosure = false);
  /** get match operator for term n
  *
  * If n has a kind that we index, this function will
  * typically return n.getOperator().
  *
  * However, for parametric operators f, the match operator is an arbitrary
  * chosen f-application.  For example, consider array select:
  * A : (Array Int Int)
  * B : (Array Bool Int)
  * We require that terms like (select A 1) and (select B 2) are indexed in
  * separate
  * data structures despite the fact that
  *    (select A 1).getOperator()==(select B 2).getOperator().
  * Hence, for the above terms, we may return:
  * getMatchOperator( (select A 1) ) = (select A 1), and
  * getMatchOperator( (select B 2) ) = (select B 2).
  * The match operator is the first instance of an application of the parametric
  * operator of its type.
  *
  * If n has a kind that we do not index (like PLUS),
  * then this function returns Node::null().
  */
  Node getMatchOperator(Node n);
  /** get term arg index for all f-applications in the current context */
  TNodeTrie* getTermArgTrie(Node f);
  /** get the term arg trie for f-applications in the equivalence class of eqc.
   */
  TNodeTrie* getTermArgTrie(Node eqc, Node f);
  /** get congruent term
  * If possible, returns a term t such that:
  * (1) t is a term that is currently indexed by this database,
  * (2) t is of the form f( t1, ..., tk ) and n is of the form f( s1, ..., sk ),
  *     where ti is in the equivalence class of si for i=1...k.
  */
  TNode getCongruentTerm(Node f, Node n);
  /** get congruent term
  * If possible, returns a term t such that:
  * (1) t is a term that is currently indexed by this database,
  * (2) t is of the form f( t1, ..., tk ) where ti is in the
  *     equivalence class of args[i] for i=1...k.
  */
  TNode getCongruentTerm(Node f, std::vector<TNode>& args);
  /** in relevant domain
  * Returns true if there is at least one term t such that:
  * (1) t is a term that is currently indexed by this database,
  * (2) t is of the form f( t1, ..., tk ) and ti is in the
  *     equivalence class of r.
  */
  bool inRelevantDomain(TNode f, unsigned i, TNode r);
  /** evaluate term
   *
   * Returns a term n' such that n = n' is entailed based on the equality
   * information qy.  This function may generate new terms. In particular,
   * we typically rewrite subterms of n of maximal size to terms that exist in
   * the equality engine specified by qy.
   *
   * useEntailmentTests is whether to call the theory engine's entailmentTest
   * on literals n for which this call fails to find a term n' that is
   * equivalent to n, for increased precision. This is not frequently used.
   *
   * The vector exp stores the explanation for why n evaluates to that term,
   * that is, if this call returns a non-null node n', then:
   *   exp => n = n'
   *
   * If reqHasTerm, then we require that the returned term is a Boolean
   * combination of terms that exist in the equality engine used by this call.
   * If no such term is constructable, this call returns null. The motivation
   * for setting this to true is to "fail fast" if we require the return value
   * of this function to only involve existing terms. This is used e.g. in
   * the "propagating instances" portion of conflict-based instantiation
   * (quant_conflict_find.h).
   */
  Node evaluateTerm(TNode n,
                    std::vector<Node>& exp,
                    EqualityQuery* qy = NULL,
                    bool useEntailmentTests = false,
                    bool reqHasTerm = false);
  /** same as above, without exp */
  Node evaluateTerm(TNode n,
                    EqualityQuery* qy = NULL,
                    bool useEntailmentTests = false,
                    bool reqHasTerm = false);
  /** get entailed term
   *
  * If possible, returns a term n' such that:
  * (1) n' exists in the current equality engine (as specified by qy),
  * (2) n = n' is entailed in the current context.
  * It returns null if no such term can be found.
  * Wrt evaluateTerm, this version does not construct new terms, and
  * thus is less aggressive.
  */
  TNode getEntailedTerm(TNode n, EqualityQuery* qy = NULL);
  /** get entailed term
   *
  * If possible, returns a term n' such that:
  * (1) n' exists in the current equality engine (as specified by qy),
  * (2) n * subs = n' is entailed in the current context, where * is denotes
  * substitution application.
  * It returns null if no such term can be found.
  * subsRep is whether the substitution maps to terms that are representatives
  * according to qy.
  * Wrt evaluateTerm, this version does not construct new terms, and
  * thus is less aggressive.
  */
  TNode getEntailedTerm(TNode n,
                        std::map<TNode, TNode>& subs,
                        bool subsRep,
                        EqualityQuery* qy = NULL);
  /** is entailed
  * Checks whether the current context entails n with polarity pol, based on the
  * equality information qy.
  * Returns true if the entailment can be successfully shown.
  */
  bool isEntailed(TNode n, bool pol, EqualityQuery* qy = NULL);
  /** is entailed
   *
  * Checks whether the current context entails ( n * subs ) with polarity pol,
  * based on the equality information qy,
  * where * denotes substitution application.
  * subsRep is whether the substitution maps to terms that are representatives
  * according to qy.
  */
  bool isEntailed(TNode n,
                  std::map<TNode, TNode>& subs,
                  bool subsRep,
                  bool pol,
                  EqualityQuery* qy = NULL);
  /** is the term n active in the current context?
   *
  * By default, all terms are active. A term is inactive if:
  * (1) it is congruent to another term
  * (2) it is irrelevant based on the term database mode. This includes terms
  * that only appear in literals that are not relevant.
  * (3) it contains instantiation constants (used for CEGQI and cannot be used
  * in instantiation).
  * (4) it is explicitly set inactive by a call to setTermInactive(...).
  * We store whether a term is inactive in a SAT-context-dependent map.
  */
  bool isTermActive(Node n);
  /** set that term n is inactive in this context. */
  void setTermInactive(Node n);
  /** has term current
   *
   * This function is used in cases where we restrict which terms appear in the
   * database, such as for heuristics used in local theory extensions
   * and for --term-db-mode=relevant.
   * It returns whether the term n should be indexed in the current context.
   *
   * If the argument useMode is true, then this method returns a value based on
   * the option options::termDbMode().
   * Otherwise, it returns the lookup in the map d_has_map.
   */
  bool hasTermCurrent(Node n, bool useMode = true);
  /** is term eligble for instantiation? */
  bool isTermEligibleForInstantiation(TNode n, TNode f);
  /** get eligible term in equivalence class of r */
  Node getEligibleTermInEqc(TNode r);
  /** is r a inst closure node?
   * This terminology was used for specifying
   * a particular status of nodes for
   * Bansal et al., CAV 2015.
   */
  bool isInstClosure(Node r);
  /** get higher-order type match predicate
   *
   * This predicate is used to force certain functions f of type tn to appear as
   * first-class representatives in the quantifier-free UF solver. For a typical
   * use case, we call getHoTypeMatchPredicate which returns a fresh predicate
   * P of type (tn -> Bool). Then, we add P( f ) as a lemma.
   */
  Node getHoTypeMatchPredicate(TypeNode tn);

 private:
  /** reference to the quantifiers engine */
  QuantifiersEngine* d_quantEngine;
  /** terms processed */
  std::unordered_set< Node, NodeHashFunction > d_processed;
  /** terms processed */
  std::unordered_set< Node, NodeHashFunction > d_iclosure_processed;
  /** select op map */
  std::map< Node, std::map< TypeNode, Node > > d_par_op_map;
  /** whether master equality engine is UF-inconsistent */
  bool d_consistent_ee;
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** list of all operators */
  std::vector<Node> d_ops;
  /** map from operators to ground terms for that operator */
  std::map< Node, std::vector< Node > > d_op_map;
  /** map from type nodes to terms of that type */
  std::map< TypeNode, std::vector< Node > > d_type_map;
  /** map from type nodes to a fresh variable we introduced */
  std::unordered_map<TypeNode, Node, TypeNodeHashFunction> d_type_fv;
  /** inactive map */
  NodeBoolMap d_inactive_map;
  /** count of the number of non-redundant ground terms per operator */
  std::map< Node, int > d_op_nonred_count;
  /** mapping from terms to representatives of their arguments */
  std::map< TNode, std::vector< TNode > > d_arg_reps;
  /** map from operators to trie */
  std::map<Node, TNodeTrie> d_func_map_trie;
  std::map<Node, TNodeTrie> d_func_map_eqc_trie;
  /** mapping from operators to their representative relevant domains */
  std::map< Node, std::map< unsigned, std::vector< Node > > > d_func_map_rel_dom;
  /** has map */
  std::map< Node, bool > d_has_map;
  /** map from reps to a term in eqc in d_has_map */
  std::map<Node, Node> d_term_elig_eqc;
  /**
   * Dummy predicate that states terms should be considered first-class members
   * of equality engine (for higher-order).
   */
  std::map<TypeNode, Node> d_ho_type_match_pred;
  /** set has term */
  void setHasTerm( Node n );
  /** helper for evaluate term */
  Node evaluateTerm2(TNode n,
                     std::map<TNode, Node>& visited,
                     std::vector<Node>& exp,
                     EqualityQuery* qy,
                     bool useEntailmentTests,
                     bool computeExp,
                     bool reqHasTerm);
  /** helper for get entailed term */
  TNode getEntailedTerm2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, EqualityQuery * qy );
  /** helper for is entailed */
  bool isEntailed2( TNode n, std::map< TNode, TNode >& subs, bool subsRep, bool hasSubs, bool pol, EqualityQuery * qy );
  /** compute uf eqc terms :
  * Ensure entries for f are in d_func_map_eqc_trie for all equivalence classes
  */
  void computeUfEqcTerms( TNode f );
  /** compute uf terms
  * Ensure that an entry for f is in d_func_map_trie
  */
  void computeUfTerms( TNode f );
  /** compute arg reps
  * Ensure that an entry for n is in d_arg_reps
  */
  void computeArgReps(TNode n);
  //------------------------------higher-order term indexing
  /**
   * Map from non-variable function terms to the operator used to purify it in
   * this database. For details, see addTermHo.
   */
  std::map<Node, Node> d_ho_fun_op_purify;
  /**
   * Map from terms to the term that they purified. For details, see addTermHo.
   */
  std::map<Node, Node> d_ho_purify_to_term;
  /**
   * Map from terms in the domain of the above map to an equality between that
   * term and its range in the above map.
   */
  std::map<Node, Node> d_ho_purify_to_eq;
  /** a map from matchable operators to their representative */
  std::map< TNode, TNode > d_ho_op_rep;
  /** for each representative matchable operator, the list of other matchable operators in their equivalence class */
  std::map<TNode, std::vector<TNode> > d_ho_op_slaves;
  /** add term higher-order
   *
   * This registers additional terms corresponding to (possibly multiple)
   * purifications of a higher-order term n.
   *
   * Consider the example:
   *    g : Int -> Int, f : Int x Int -> Int
   *    constraints: (@ f 0) = g, (f 0 1) = (@ (@ f 0) 1) = 3
   *    pattern: (g x)
   * where @ is HO_APPLY.
   * We have that (g x){ x -> 1 } is an E-match for (@ (@ f 0) 1).
   * With the standard registration in addTerm, we construct term indices for
   *   f, g, @ : Int x Int -> Int, @ : Int -> Int.
   * However, to match (g x) with (@ (@ f 0) 1), we require that
   *   [1] -> (@ (@ f 0) 1)
   * is an entry in the term index of g. To do this, we maintain a term
   * index for a fresh variable pfun, the purification variable for
   * (@ f 0). Thus, we register the term (pfun 1) in the call to this function
   * for (@ (@ f 0) 1). This ensures that, when processing the equality
   * (@ f 0) = g, we merge the term indices of g and pfun. Hence, the entry
   *   [1] -> (@ (@ f 0) 1)
   * is added to the term index of g, assuming g is the representative of
   * the equivalence class of g and pfun.
   *
   * Above, we set d_ho_fun_op_purify[(@ f 0)] = pfun, and
   * d_ho_purify_to_term[(pfun 1)] = (@ (@ f 0) 1).
   */
  void addTermHo(Node n,
                 std::set<Node>& added,
                 bool withinQuant,
                 bool withinInstClosure);
  /** get operator representative */
  Node getOperatorRepresentative( TNode op ) const;
  //------------------------------end higher-order term indexing
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */

/*********************                                                        */
/*! \file term_database.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief term database class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include <map>
#include <unordered_set>

#include "expr/attribute.h"
#include "theory/theory.h"
#include "theory/type_enumerator.h"
#include "theory/quantifiers/quant_util.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace inst{
  class Trigger;
  class HigherOrderTrigger;
}

namespace quantifiers {

/** Term arg trie class
*
* This also referred to as a "term index" or a "signature table".
*
* This data structure stores a set expressions, indexed by representatives of
* their arguments.
*
* For example, consider the equivalence classes :
*
* { a, d, f( d, c ), f( a, c ) }
* { b, f( b, d ) }
* { c, f( b, b ) }
*
* where the first elements ( a, b, c ) are the representatives of these classes.
* The TermArgTrie t we may build for f is :
*
* t :
*   t.d_data[a] :
*     t.d_data[a].d_data[c] :
*       t.d_data[a].d_data[c].d_data[f(d,c)] : (leaf)
*   t.d_data[b] :
*     t.d_data[b].d_data[b] :
*       t.d_data[b].d_data[b].d_data[f(b,b)] : (leaf)
*     t.d_data[b].d_data[d] :
*       t.d_data[b].d_data[d].d_data[f(b,d)] : (leaf)
*
* Leaf nodes store the terms that are indexed by the arguments, for example
* term f(d,c) is indexed by the representative arguments (a,c), and is stored
* as a the (single) key in the data of t.d_data[a].d_data[c].
*/
class TermArgTrie {
public:
  /** the data */
  std::map< TNode, TermArgTrie > d_data;
public:
 /** for leaf nodes : does this trie have data? */
 bool hasNodeData() { return !d_data.empty(); }
 /** for leaf nodes : get term corresponding to this leaf */
 TNode getNodeData() { return d_data.begin()->first; }
 /** exists term
 * Returns the term that is indexed by reps, if one exists, or
 * or returns null otherwise.
 */
 TNode existsTerm(std::vector<TNode>& reps, int argIndex = 0);
 /** add or get term
 * Returns the term that is previously indexed by reps, if one exists, or
 * Adds n to the trie, indexed by reps, and returns n.
 */
 TNode addOrGetTerm(TNode n, std::vector<TNode>& reps, int argIndex = 0);
 /** add term
 * Returns false if a term is previously indexed by reps.
 * Returns true if no term is previously indexed by reps,
 *   and adds n to the trie, indexed by reps, and returns n.
 */
 bool addTerm(TNode n, std::vector<TNode>& reps, int argIndex = 0);
 /** debug print this trie */
 void debugPrint(const char* c, Node n, unsigned depth = 0);
 /** clear all data from this trie */
 void clear() { d_data.clear(); }
};/* class TermArgTrie */

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
 * (2) Build TermArgTrie objects that index all ground terms, per operator.
 *
 * Like other utilities, its reset(...) function is called
 * at the beginning of full or last call effort checks.
 * This initializes the database for the round. However,
 * notice that TermArgTrie objects are computed
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
  * Returns the first ground term of type tn,
  * or makes one if none exist.
  */
  Node getOrMakeTypeGroundTerm(TypeNode tn);
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
  TermArgTrie* getTermArgTrie(Node f);
  /** get the term arg trie for f-applications in the equivalence class of eqc.
   */
  TermArgTrie* getTermArgTrie(Node eqc, Node f);
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
  * we typically rewrite maximal
  * subterms of n to terms that exist in the equality engine specified by qy.
  *
  * useEntailmentTests is whether to use the theory engine's entailmentCheck
  * call, for increased precision. This is not frequently used.
  */
  Node evaluateTerm(TNode n,
                    EqualityQuery* qy = NULL,
                    bool useEntailmentTests = false);
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
  */
  bool hasTermCurrent(Node n, bool useMode = true);
  /** is term eligble for instantiation? */
  bool isTermEligibleForInstantiation(TNode n, TNode f, bool print = false);
  /** get eligible term in equivalence class of r */
  Node getEligibleTermInEqc(TNode r);
  /** is r a inst closure node?
   * This terminology was used for specifying
   * a particular status of nodes for
   * Bansal et al., CAV 2015.
   */
  bool isInstClosure(Node r);

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
  std::map< Node, TermArgTrie > d_func_map_trie;
  std::map< Node, TermArgTrie > d_func_map_eqc_trie;
  /** mapping from operators to their representative relevant domains */
  std::map< Node, std::map< unsigned, std::vector< Node > > > d_func_map_rel_dom;
  /** has map */
  std::map< Node, bool > d_has_map;
  /** map from reps to a term in eqc in d_has_map */
  std::map< Node, Node > d_term_elig_eqc;  
  /** set has term */
  void setHasTerm( Node n );
  /** helper for evaluate term */
  Node evaluateTerm2( TNode n, std::map< TNode, Node >& visited, EqualityQuery * qy, bool useEntailmentTests );
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
  /** a map from matchable operators to their representative */
  std::map< TNode, TNode > d_ho_op_rep;
  /** for each representative matchable operator, the list of other matchable operators in their equivalence class */
  std::map< TNode, std::vector< TNode > > d_ho_op_rep_slaves;
  /** get operator representative */
  Node getOperatorRepresentative( TNode op ) const;
  //------------------------------end higher-order term indexing
};/* class TermDb */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__QUANTIFIERS__TERM_DATABASE_H */

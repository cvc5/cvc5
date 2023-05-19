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
 * Term database class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_H
#define CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_H

#include <map>
#include <unordered_map>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/attribute.h"
#include "expr/node_trie.h"
#include "theory/quantifiers/quant_util.h"
#include "theory/theory.h"
#include "theory/type_enumerator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class QuantifiersInferenceManager;
class QuantifiersRegistry;

/** Context-dependent list of nodes */
class DbList
{
 public:
  DbList(context::Context* c) : d_list(c) {}
  /** The list */
  context::CDList<Node> d_list;
};

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
  using NodeBoolMap = context::CDHashMap<Node, bool>;
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;
  using TypeNodeDbListMap =
      context::CDHashMap<TypeNode, std::shared_ptr<DbList>>;
  using NodeDbListMap = context::CDHashMap<Node, std::shared_ptr<DbList>>;

 public:
  TermDb(Env& env, QuantifiersState& qs, QuantifiersRegistry& qr);
  virtual ~TermDb();
  /** Finish init, which sets the inference manager */
  void finishInit(QuantifiersInferenceManager* qim);
  /** presolve (called once per user check-sat) */
  void presolve() override;
  /** reset (calculate which terms are active) */
  bool reset(Theory::Effort effort) override;
  /** register quantified formula */
  void registerQuantifier(Node q) override;
  /** identify */
  std::string identify() const override { return "TermDb"; }
  /** get number of operators */
  size_t getNumOperators() const;
  /** get operator at index i */
  Node getOperator(size_t i) const;
  /** ground terms for operator
  * Get the number of ground terms with operator f that have been added to the
  * database
  */
  size_t getNumGroundTerms(TNode f) const;
  /** get ground term for operator
  * Get the i^th ground term with operator f that has been added to the database
  */
  Node getGroundTerm(TNode f, size_t i) const;
  /** Get ground term list */
  DbList* getGroundTermList(TNode f) const;
  /** get num type terms
  * Get the number of ground terms of tn that have been added to the database
  */
  size_t getNumTypeGroundTerms(TypeNode tn) const;
  /** get type ground term
  * Returns the i^th ground term of type tn
  */
  Node getTypeGroundTerm(TypeNode tn, size_t i) const;
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
  /**
   * Add a term to the database, which registers it as a term that may be
   * matched with via E-matching, and can be used in entailment tests below.
   */
  void addTerm(Node n);
  /** Get the currently added ground terms of the given type */
  DbList* getOrMkDbListForType(TypeNode tn);
  /** Get the currently added ground terms for the given operator */
  DbList* getOrMkDbListForOp(TNode op);
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
   * The match operator is the first instance of an application of the
   * parametric operator of its type.
   *
   * If n has a kind that we do not index (like ADD),
   * then this function returns Node::null().
   */
  Node getMatchOperator(TNode n);
  /** Is matchable? true if the above method is non-null */
  bool isMatchable(TNode n);
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
   * If not possible, return the null node.
   */
  TNode getCongruentTerm(Node f, const std::vector<TNode>& args);
  /** in relevant domain
  * Returns true if there is at least one term t such that:
  * (1) t is a term that is currently indexed by this database,
  * (2) t is of the form f( t1, ..., tk ) and ti is in the
  *     equivalence class of r.
  */
  bool inRelevantDomain(TNode f, size_t i, TNode r);
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
   * the option termDbMode.
   * Otherwise, it returns the lookup in the map d_has_map.
   */
  bool hasTermCurrent(Node n, bool useMode = true);
  /** is term eligble for instantiation? */
  bool isTermEligibleForInstantiation(TNode n, TNode f);
  /** get eligible term in equivalence class of r */
  Node getEligibleTermInEqc(TNode r);

 protected:
  /** The quantifiers state object */
  QuantifiersState& d_qstate;
  /** Pointer to the quantifiers inference manager */
  QuantifiersInferenceManager* d_qim;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** A context for the data structures below, when not context-dependent */
  context::Context d_termsContext;
  /** The context we are using for the data structures below */
  context::Context* d_termsContextUse;
  /** terms processed */
  NodeSet d_processed;
  /** map from types to ground terms for that type */
  TypeNodeDbListMap d_typeMap;
  /** list of all operators */
  NodeList d_ops;
  /** map from operators to ground terms for that operator */
  NodeDbListMap d_opMap;
  /** select op map */
  std::map< Node, std::map< TypeNode, Node > > d_par_op_map;
  /** whether master equality engine is UF-inconsistent */
  bool d_consistent_ee;
  /** boolean terms */
  Node d_true;
  Node d_false;
  /** map from type nodes to a fresh variable we introduced */
  std::unordered_map<TypeNode, Node> d_type_fv;
  /** inactive map */
  NodeBoolMap d_inactive_map;
  /** count of the number of non-redundant ground terms per operator */
  std::map< Node, int > d_op_nonred_count;
  /** mapping from terms to representatives of their arguments */
  std::map< TNode, std::vector< TNode > > d_arg_reps;
  /** map from operators to trie */
  std::map<Node, TNodeTrie> d_func_map_trie;
  std::map<Node, TNodeTrie> d_func_map_eqc_trie;
  /**
   * Mapping from operators to their representative relevant domains. The
   * size of the range is equal to the arity of the domain symbol. The
   * terms in each vector are the representatives that occur in a term for
   * that argument position (see inRelevantDomain).
   */
  std::map<Node, std::vector<std::vector<TNode>>> d_fmapRelDom;
  /** has map */
  std::map< Node, bool > d_has_map;
  /** map from reps to a term in eqc in d_has_map */
  std::map<Node, Node> d_term_elig_eqc;
  /**
   * Dummy predicate that states terms should be considered first-class members
   * of equality engine (for higher-order).
   */
  std::map<TypeNode, Node> d_ho_type_match_pred;
  //----------------------------- implementation-specific
  /**
   * Reset internal, called when reset(e) is called. Returning false will cause
   * the overall reset to terminate early, returning false.
   */
  virtual bool resetInternal(Theory::Effort e);
  /**
   * Finish reset internal, called at the end of reset(e). Returning false will
   * cause the overall reset to return false.
   */
  virtual bool finishResetInternal(Theory::Effort e);
  /** Add term internal, called when addTerm(n) is called */
  virtual void addTermInternal(Node n);
  /** Get operators that we know are equivalent to f, typically only f itself */
  virtual void getOperatorsFor(TNode f, std::vector<TNode>& ops);
  /** get the chosen representative for operator op */
  virtual Node getOperatorRepresentative(TNode op) const;
  /**
   * This method is called when terms a and b are indexed by the same operator,
   * and have equivalent arguments. This method checks if we are in conflict,
   * which is the case if a and b are disequal in the equality engine.
   * If so, it adds the set of literals that are implied but do not hold, e.g.
   * the equality (= a b).
   */
  virtual bool checkCongruentDisequal(TNode a, TNode b, std::vector<Node>& exp);
  //----------------------------- end implementation-specific
  /** set has term */
  void setHasTerm( Node n );
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
};/* class TermDb */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_H */

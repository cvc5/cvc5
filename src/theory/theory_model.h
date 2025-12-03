/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__THEORY_MODEL_H
#define CVC5__THEORY__THEORY_MODEL_H

#include <unordered_map>
#include <unordered_set>

#include "expr/node_trie.h"
#include "smt/env_obj.h"
#include "theory/ee_setup_info.h"
#include "theory/rep_set.h"
#include "theory/type_enumerator.h"
#include "theory/type_set.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {

class Env;

namespace theory {

/** Theory Model class.
 *
 * This class represents a model produced by the TheoryEngine.
 * The data structures used to represent a model are:
 * (1) d_equalityEngine : an equality engine object, which stores
 *     an equivalence relation over all terms that exist in
 *     the current set of assertions.
 * (2) d_reps : a map from equivalence class representatives of
 *     the equality engine to the (constant) representatives
 *     assigned to that equivalence class.
 * (3) d_uf_models : a map from uninterpreted functions to their
 *     lambda representation.
 * (4) d_rep_set : a data structure that allows interpretations
 *     for types to be represented as terms. This is useful for
 *     finite model finding.
 * Additionally, models are dependent on top-level substitutions stored in the
 * d_env class.
 *
 * These data structures are built after a full effort check with
 * no lemmas sent, within a call to:
 *    TheoryEngineModelBuilder::buildModel(...)
 * which includes subcalls to TheoryX::collectModelInfo(...) calls.
 *
 * These calls may modify the model object using the interface
 * functions below, including:
 * - assertEquality, assertPredicate, assertSkeleton,
 *   assertEqualityEngine.
 * - assignFunctionDefinition
 *
 * This class provides several interface functions:
 * - hasTerm, getRepresentative, areEqual, areDisequal
 * - getEqualityEngine
 * - getRepSet
 * - hasAssignedFunctionDefinition
 * - getValue
 *
 * The above functions can be used for a model m after it has been
 * successfully built, i.e. when m->isBuiltSuccess() returns true.
 *
 * Additionally, all of the above functions, with the exception of getValue,
 * can be used during step (5) of TheoryEngineModelBuilder::buildModel, as
 * documented in theory_model_builder.h. In particular, we make calls to the
 * above functions such as getRepresentative() when assigning total
 * interpretations for uninterpreted functions.
 */
class TheoryModel : protected EnvObj
{
  friend class TheoryEngineModelBuilder;

 public:
  TheoryModel(Env& env, std::string name, bool enableFuncModels);
  virtual ~TheoryModel();
  /**
   * Finish init, where ee is the equality engine the model should use.
   */
  void finishInit(eq::EqualityEngine* ee);

  /** reset the model */
  virtual void reset();
  //---------------------------- for building the model
  /** assert equality holds in the model
   *
   * This method returns true if and only if the equality engine of this model
   * is consistent after asserting the equality to this model.
   */
  bool assertEquality(TNode a, TNode b, bool polarity);
  /** assert predicate holds in the model
   *
   * This method returns true if and only if the equality engine of this model
   * is consistent after asserting the predicate to this model.
   */
  bool assertPredicate(TNode a, bool polarity);
  /** assert all equalities/predicates in equality engine hold in the model
   *
   * This method returns true if and only if the equality engine of this model
   * is consistent after asserting the equality engine to this model.
   */
  bool assertEqualityEngine(const eq::EqualityEngine* ee,
                            const std::set<Node>* termSet = NULL);
  /** assert skeleton
   *
   * This method gives a "skeleton" for the model value of the equivalence
   * class containing n. This should be an application of interpreted function
   * (e.g. datatype constructor, array store, set union chain). The subterms of
   * this term that are variables or terms that belong to other theories will
   * be filled in with model values.
   *
   * For example, if we call assertSkeleton on (C x y) where C is a datatype
   * constructor and x and y are variables, then the equivalence class of
   * (C x y) will be interpreted in m as (C x^m y^m) where
   * x^m = m->getValue( x ) and y^m = m->getValue( y ).
   *
   * It should be called during model generation, before final representatives
   * are chosen. In the case of TheoryEngineModelBuilder, it should be called
   * during Theory's collectModelInfo( ... ) functions.
   */
  void assertSkeleton(TNode n);
  /** set assignment exclusion set
   *
   * This method sets the "assignment exclusion set" for term n. This is a
   * set of terms whose value n must be distinct from in the model.
   *
   * This method should be used sparingly, and in a way such that model
   * building is still guaranteed to succeed. Term n is intended to be an
   * assignable term, typically of finite type. Thus, for example, this method
   * should not be called with a vector eset that is greater than the
   * cardinality of the type of n. Additionally, this method should not be
   * called in a way that introduces cyclic dependencies on the assignment order
   * of terms in the model. For example, providing { y } as the assignment
   * exclusion set of x and { x } as the assignment exclusion set of y will
   * cause model building to fail.
   *
   * The vector eset should contain only terms that occur in the model, or
   * are constants.
   *
   * Additionally, we (currently) require that an assignment exclusion set
   * should not be set for two terms in the same equivalence class, or to
   * equivalence classes with an assignable term. Otherwise an
   * assertion will be thrown by TheoryEngineModelBuilder during model building.
   */
  void setAssignmentExclusionSet(TNode n, const std::vector<Node>& eset);
  /** set assignment exclusion set group
   *
   * Given group = { x_1, ..., x_n }, this is semantically equivalent to calling
   * the above method on the following pairs of arguments:
   *   x1, eset
   *   x2, eset + { x_1 }
   *   ...
   *   xn, eset + { x_1, ..., x_{n-1} }
   * Similar restrictions should be considered as above when applying this
   * method to ensure that model building will succeed. Notice that for
   * efficiency, the implementation of how the above information is stored
   * may avoid constructing n copies of eset.
   */
  void setAssignmentExclusionSetGroup(const std::vector<TNode>& group,
                                      const std::vector<Node>& eset);
  /** get assignment exclusion set for term n
   *
   * If n has been given an assignment exclusion set, then this method returns
   * true and the set is added to eset. Otherwise, the method returns false.
   *
   * Additionally, if n was assigned an assignment exclusion set via a call to
   * setAssignmentExclusionSetGroup, it adds all members that were passed
   * in the first argument of that call to the vector group. Otherwise, it
   * adds n itself to group.
   */
  bool getAssignmentExclusionSet(TNode n,
                                 std::vector<Node>& group,
                                 std::vector<Node>& eset);
  /** have any assignment exclusion sets been created? */
  bool hasAssignmentExclusionSets() const;
  /** set unevaluate/semi-evaluated kind
   *
   * This informs this model how it should interpret applications of terms with
   * kind k in getModelValue. We distinguish four categories of kinds:
   *
   * [1] "Evaluated"
   * This includes (standard) interpreted symbols like NOT, ADD, SET_UNION,
   * etc. These operators can be characterized by the invariant that they are
   * "evaluatable". That is, if they are applied to only constants, the rewriter
   * is guaranteed to rewrite the application to a constant. When getting
   * the model value of <k>( t1...tn ) where k is a kind of this category, we
   * compute the (constant) value of t1...tn, say this returns c1...cn, we
   * return the (constant) result of rewriting <k>( c1...cn ).
   *
   * [2] "Unevaluated"
   * This includes interpreted symbols like FORALL, EXISTS,
   * CARDINALITY_CONSTRAINT, that are not evaluatable. When getting a model
   * value for a term <k>( t1...tn ) where k is a kind of this category, we
   * check whether <k>( t1...tn ) exists in the equality engine of this model.
   * If it does, we return its representative, otherwise we return the term
   * itself.
   *
   * [3] "Semi-evaluated"
   * This includes kinds like BITVECTOR_ACKERMANNIZE_UDIV, APPLY_SELECTOR and.
   * SEQ_NTH. Like unevaluated kinds, these kinds do not have an evaluator for
   * (some) inputs. In contrast to unevaluated kinds, we interpret a term
   * <k>( t1...tn ) not appearing in the equality engine as an arbitrary value
   * instead of the term itself.
   *
   * [4] APPLY_UF, where getting the model value depends on an internally
   * constructed representation of a lambda model value (d_uf_models).
   * It is optional whether this kind is "evaluated" or "semi-evaluated".
   * In the case that it is "evaluated", get model rewrites the application
   * of the lambda model value of its operator to its evaluated arguments.
   *
   * By default, all kinds are considered "evaluated". The following methods
   * change the interpretation of various (non-APPLY_UF) kinds to one of the
   * above categories and should be called by the theories that own the kind
   * during Theory::finishInit. We set APPLY_UF to be semi-interpreted when
   * this model does not enabled function values (this is the case for the model
   * of TheoryEngine when the option assignFunctionValues is set to false).
   */
  void setUnevaluatedKind(Kind k);
  void setSemiEvaluatedKind(Kind k);
  /**
   * Set irrelevant kind. These kinds do not impact model generation, that is,
   * registered terms in theories of this kind do not need to be sent to
   * the model. An example is APPLY_TESTER.
   */
  void setIrrelevantKind(Kind k);
  /**
   * Get the set of irrelevant kinds that have been registered by the above
   * method.
   */
  const std::set<Kind>& getIrrelevantKinds() const;
  /** is legal elimination
   *
   * Returns true if x -> val is a legal elimination of variable x.
   * In particular, this ensures that val does not have any subterms that
   * are of unevaluated kinds.
   */
  bool isLegalElimination(TNode x, TNode val);
  //---------------------------- end building the model

  // ------------------- general equality queries
  /** does the equality engine of this model have term a? */
  bool hasTerm(TNode a);
  /** get the representative of a in the equality engine of this model */
  Node getRepresentative(TNode a) const;
  /** are a and b equal in the equality engine of this model? */
  bool areEqual(TNode a, TNode b) const;
  /** are a and b disequal in the equality engine of this model? */
  bool areDisequal(TNode a, TNode b);
  /** get the equality engine for this model */
  eq::EqualityEngine* getEqualityEngine() { return d_equalityEngine; }
  // ------------------- end general equality queries

  /**
   * Get value function.
   * This should be called only after a ModelBuilder has called buildModel(...)
   * on this model.
   * @param n The term to get the value of.
   * @return The value of n.
   */
  Node getValue(TNode n) const;

  /**
   * Simplify n based on the values in this class. This applies a substitution
   * over the free symbols on n and rewrites.
   * This should be called only after a ModelBuilder has called buildModel(...)
   * on this model.
   * @param n The term to simplify.
   * @return The simplified form of n.
   */
  Node simplify(TNode n) const;

  //---------------------------- separation logic
  /** set the heap and value sep.nil is equal to */
  void setHeapModel(Node h, Node neq);
  /** get the heap and value sep.nil is equal to */
  bool getHeapModel(Node& h, Node& neq) const;
  //---------------------------- end separation logic

  /** get domain elements for uninterpreted sort t */
  std::vector<Node> getDomainElements(TypeNode t) const;
  /** get the representative set object */
  const RepSet* getRepSet() const { return &d_rep_set; }
  /** get the representative set object (FIXME: remove this, see #1199) */
  RepSet* getRepSetPtr() { return &d_rep_set; }

  //---------------------------- model cores
  /** True if a model core has been computed for this model. */
  bool isUsingModelCore() const;
  /** set using model core */
  void setUsingModelCore();
  /** record model core symbol */
  void recordModelCoreSymbol(Node sym);
  /** Return whether symbol expr is in the model core. */
  bool isModelCoreSymbol(Node sym) const;
  //---------------------------- end model cores

  //---------------------------- function values
  /** Does this model have terms for the given uninterpreted function? */
  bool hasUfTerms(Node f) const;
  /** Get the terms for uninterpreted function f */
  const std::vector<Node>& getUfTerms(Node f) const;
  /** are function values enabled? */
  bool areFunctionValuesEnabled() const;
  /** assign function value f to definition f_def */
  void assignFunctionDefinition(Node f, Node f_def) const;
  /** have we assigned function f? */
  bool hasAssignedFunctionDefinition(Node f) const;
  //---------------------------- end function values
  /** Get the name of this model */
  const std::string& getName() const;
  /**
   * For debugging, print the equivalence classes of the underlying equality
   * engine.
   */
  std::string debugPrintModelEqc() const;

  /**
   * Is the node n a "value"? This is true if n is a "base value", where
   * a base value is one where isConst() returns true, a constant-like
   * value (e.g. a real algebraic number) or if n is a lambda or witness
   * term.
   *
   * We also return true for rewritten nodes whose leafs are base values.
   * For example, (str.++ (witness ((x String)) (= (str.len x) 1000)) "A") is
   * a value.
   */
  bool isValue(TNode node) const;

 protected:
  /**
   * Get cardinality for sort, where t is an uninterpreted sort.
   * @param t The sort.
   * @return the cardinality of the sort, which is the number of representatives
   * for that sort, or 1 if none exist.
   */
  size_t getCardinality(const TypeNode& t) const;
  /**
   * Assign that n is the representative of the equivalence class r.
   * @param r The equivalence class
   * @param n Its assigned representative
   * @param isFinal Whether the assignment is final, which impacts whether
   * we additionally assign function definitions if we are higher-order and
   * r is a function.
   */
  void assignRepresentative(const Node& r, const Node& n, bool isFinal = true);
  /**
   * Assign function f, which is called on demand when the model for f is
   * required by this class (e.g. in getValue or getRepresentative).
   * If not higher-order, this construction is based on "table form". For
   * example:
   * (f 0 1) = 1
   * (f 0 2) = 2
   * (f 1 1) = 3
   * ...
   * becomes:
   * f = (lambda xy. (ite (and (= x 0) (= y 1)) 1
   *                 (ite (and (= x 0) (= y 2)) 2
   *                 (ite (and (= x 1) (= y 1)) 3 ...))).
   * If higher-order, we call assignFunctionDefaultHo instead.
   * @param f The function to assign.
   */
  void assignFunctionDefault(Node f) const;
  /**
   * Assign function f when the logic is higher-order. This is called on demand
   * when the model for f is required by his class.
   * This construction is based on "dag form". For example:
   * (f 0 1) = 1
   * (f 0 2) = 2
   * (f 1 1) = 3
   * ...
   * becomes:
   * f = (lambda xy. (ite (= x 0) (ite (= y 1) 1
   *                              (ite (= y 2) 2 ...))
   *                 (ite (= x 1) (ite (= y 1) 3 ...)
   *                              ...))
   *
   * where the above is represented as a directed acyclic graph (dag).
   * This construction is accomplished by assigning values to (f c)
   * terms before f, e.g.
   * (f 0) = (lambda y. (ite (= y 1) 1
   *                    (ite (= y 2) 2 ...))
   * (f 1) = (lambda y. (ite (= y 1) 3 ...))
   * where
   * f = (lambda xy. (ite (= x 0) ((f 0) y)
   *                 (ite (= x 1) ((f 1) y) ...))
   * @param f The function to assign.
   */
  void assignFunctionDefaultHo(Node f) const;
  /** Unique name of this model */
  std::string d_name;
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine* d_equalityEngine;
  /** a set of kinds that are unevaluated */
  std::unordered_set<Kind, kind::KindHashFunction> d_unevaluated_kinds;
  /** a set of kinds that are semi-evaluated */
  std::unordered_set<Kind, kind::KindHashFunction> d_semi_evaluated_kinds;
  /** The set of irrelevant kinds */
  std::set<Kind> d_irrKinds;
  /**
   * Map of representatives of equality engine to used representatives in
   * representative set
   */
  mutable std::map<Node, Node> d_reps;
  /** Map of terms to their assignment exclusion set. */
  std::map<Node, std::vector<Node> > d_assignExcSet;
  /**
   * Map of terms to their "assignment exclusion set master". After a call to
   * setAssignmentExclusionSetGroup, the master of each term in group
   * (except group[0]) is set to group[0], which stores the assignment
   * exclusion set for that group in the above map.
   */
  std::map<Node, Node> d_aesMaster;
  /** Reverse of the above map */
  std::map<Node, std::vector<Node> > d_aesSlaves;
  /** stores set of representatives for each type */
  RepSet d_rep_set;
  /** true/false nodes */
  Node d_true;
  Node d_false;
  /** are we using model cores? */
  bool d_using_model_core;
  /** symbols that are in the model core */
  std::unordered_set<Node> d_model_core;
  /** Get model value function.
   *
   * This function is a helper function for getValue.
   */
  Node getModelValue(TNode n) const;
  /** add term internal
   *
   * This will do any model-specific processing necessary for n,
   * such as constraining the interpretation of uninterpreted functions.
   * This is called once for all terms in the equality engine, just before
   * a model builder constructs this model.
   */
  virtual void addTermInternal(TNode n);
  /**
   * Is base model value?  This is a helper method for isValue, returns true
   * if n is a base model value.
   */
  bool isBaseModelValue(TNode n) const;
  /** Is assignable function. This returns true if n is not a lambda. */
  bool isAssignableUf(const Node& n) const;
  /**
   * Evaluate semi-evaluated term. This determines if there is a term n' that is
   * in the equality engine of this model that is congruent to n, if so, it
   * returns the model value of n', otherwise this returns the null term.
   * @param n The term to evaluate. We assume it is in rewritten form and
   * has a semi-evaluated kind (e.g. APPLY_SELECTOR).
   * @return The entailed model value for n, if it exists.
   */
  Node evaluateSemiEvalTerm(TNode n) const;
  /**
   * @return The model values of the arguments of n.
   */
  std::vector<Node> getModelValueArgs(TNode n) const;

 private:
  /** cache for getModelValue */
  mutable std::unordered_map<Node, Node> d_modelCache;
  /** whether we have computed d_semiEvalCache yet */
  mutable bool d_semiEvalCacheSet;
  /** cache used for evaluateSemiEvalTerm */
  mutable std::unordered_map<Node, NodeTrie> d_semiEvalCache;

  //---------------------------- separation logic
  /** the value of the heap */
  Node d_sep_heap;
  /** the value of the nil element */
  Node d_sep_nil_eq;
  //---------------------------- end separation logic

  //---------------------------- function values
  /** a map from functions f to a list of all APPLY_UF terms with operator f */
  std::map<Node, std::vector<Node> > d_uf_terms;
  /** a map from functions f to a list of all HO_APPLY terms with first argument
   * f */
  std::map<Node, std::vector<Node> > d_ho_uf_terms;
  /** whether function models are enabled */
  bool d_enableFuncModels;
  /**
   * Map from function terms to the (lambda) definitions
   * After the model is built, the domain of this map is all terms of function
   * type that appear as terms in d_equalityEngine.
   */
  mutable std::map<Node, Node> d_uf_models;
  //---------------------------- end function values
};/* class TheoryModel */

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__THEORY_MODEL_H */

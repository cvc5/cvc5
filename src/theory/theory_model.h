/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Clark Barrett, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

#include "theory/ee_setup_info.h"
#include "theory/rep_set.h"
#include "theory/type_enumerator.h"
#include "theory/type_set.h"
#include "theory/uf/equality_engine.h"
#include "util/cardinality.h"

namespace cvc5 {

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
 * - hasAssignedFunctionDefinition, getFunctionsToAssign
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
class TheoryModel
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
  /** record approximation
   *
   * This notifies this model that the value of n was approximated in this
   * model such that the predicate pred (involving n) holds. For example,
   * for transcendental functions, we may determine an error bound on the
   * value of a transcendental function, say c-e <= y <= c+e where
   * c and e are constants. We call this function with n set to sin( x ) and
   * pred set to c-e <= sin( x ) <= c+e.
   *
   * If recordApproximation is called at least once during the model
   * construction process, then check-model is not guaranteed to succeed.
   * However, there are cases where we can establish the input is satisfiable
   * without constructing an exact model. For example, if x=.77, sin(x)=.7, and
   * say we have computed c=.7 and e=.01 as an approximation in the above
   * example, then we may reason that the set of assertions { sin(x)>.6 } is
   * satisfiable, albiet without establishing an exact (irrational) value for
   * sin(x).
   *
   * This function is simply for bookkeeping, it does not affect the model
   * construction process.
   */
  void recordApproximation(TNode n, TNode pred);
  /**
   * Same as above, but with a witness constant. This ensures that the
   * approximation predicate is of the form (or (= n witness) pred). This
   * is useful if the user wants to know a possible concrete value in
   * the range of the predicate.
   */
  void recordApproximation(TNode n, TNode pred, Node witness);
  /** set unevaluate/semi-evaluated kind
   *
   * This informs this model how it should interpret applications of terms with
   * kind k in getModelValue. We distinguish four categories of kinds:
   *
   * [1] "Evaluated"
   * This includes (standard) interpreted symbols like NOT, PLUS, UNION, etc.
   * These operators can be characterized by the invariant that they are
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
   * This includes kinds like BITVECTOR_ACKERMANNIZE_UDIV and others, typically
   * those that correspond to abstractions. Like unevaluated kinds, these
   * kinds do not have an evaluator. In contrast to unevaluated kinds, we
   * interpret a term <k>( t1...tn ) not appearing in the equality engine as an
   * arbitrary value instead of the term itself.
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
  Node getRepresentative(TNode a);
  /** are a and b equal in the equality engine of this model? */
  bool areEqual(TNode a, TNode b);
  /** are a and b disequal in the equality engine of this model? */
  bool areDisequal(TNode a, TNode b);
  /** get the equality engine for this model */
  eq::EqualityEngine* getEqualityEngine() { return d_equalityEngine; }
  // ------------------- end general equality queries

  /** Get value function.
   * This should be called only after a ModelBuilder
   * has called buildModel(...) on this model.
   */
  Node getValue(TNode n) const;
  /** get comments */
  void getComments(std::ostream& out) const;

  //---------------------------- separation logic
  /** set the heap and value sep.nil is equal to */
  void setHeapModel(Node h, Node neq);
  /** get the heap and value sep.nil is equal to */
  bool getHeapModel(Node& h, Node& neq) const;
  //---------------------------- end separation logic

  /** is the list of approximations non-empty? */
  bool hasApproximations() const;
  /** get approximations */
  std::vector<std::pair<Node, Node> > getApproximations() const;
  /** get domain elements for uninterpreted sort t */
  std::vector<Node> getDomainElements(TypeNode t) const;
  /** get the representative set object */
  const RepSet* getRepSet() const { return &d_rep_set; }
  /** get the representative set object (FIXME: remove this, see #1199) */
  RepSet* getRepSetPtr() { return &d_rep_set; }

  //---------------------------- model cores
  /** set using model core */
  void setUsingModelCore();
  /** record model core symbol */
  void recordModelCoreSymbol(Node sym);
  /** Return whether symbol expr is in the model core. */
  bool isModelCoreSymbol(Node sym) const;
  //---------------------------- end model cores

  /** get cardinality for sort */
  Cardinality getCardinality(TypeNode t) const;

  //---------------------------- function values
  /** Does this model have terms for the given uninterpreted function? */
  bool hasUfTerms(Node f) const;
  /** Get the terms for uninterpreted function f */
  const std::vector<Node>& getUfTerms(Node f) const;
  /** are function values enabled? */
  bool areFunctionValuesEnabled() const;
  /** assign function value f to definition f_def */
  void assignFunctionDefinition( Node f, Node f_def );
  /** have we assigned function f? */
  bool hasAssignedFunctionDefinition( Node f ) const { return d_uf_models.find( f )!=d_uf_models.end(); }
  /** get the list of functions to assign. 
  * This list will contain all terms of function type that are terms in d_equalityEngine.
  * If higher-order is enabled, we ensure that this list is sorted by type size.
  * This allows us to assign functions T -> T before ( T x T ) -> T and before ( T -> T ) -> T,
  * which is required for "dag form" model construction (see TheoryModelBuilder::assignHoFunction).
  */
  std::vector< Node > getFunctionsToAssign();
  //---------------------------- end function values
  /** Get the name of this model */
  const std::string& getName() const;
  /**
   * For debugging, print the equivalence classes of the underlying equality
   * engine.
   */
  std::string debugPrintModelEqc() const;

 protected:
  /** Reference to the environmanet */
  Env& d_env;
  /** Unique name of this model */
  std::string d_name;
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine* d_equalityEngine;
  /** approximations (see recordApproximation) */
  std::map<Node, Node> d_approximations;
  /** list of all approximations */
  std::vector<std::pair<Node, Node> > d_approx_list;
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
  std::map<Node, Node> d_reps;
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
  /** comment stream to include in printing */
  std::stringstream d_comment_str;
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
 private:
  /** cache for getModelValue */
  mutable std::unordered_map<Node, Node> d_modelCache;

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
  /** map from function terms to the (lambda) definitions
  * After the model is built, the domain of this map is all terms of function
  * type that appear as terms in d_equalityEngine.
  */
  std::map<Node, Node> d_uf_models;
  //---------------------------- end function values
};/* class TheoryModel */

}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__THEORY_MODEL_H */

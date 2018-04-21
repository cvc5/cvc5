/*********************                                                        */
/*! \file theory_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_MODEL_H
#define __CVC4__THEORY__THEORY_MODEL_H

#include <unordered_map>
#include <unordered_set>

#include "smt/model.h"
#include "theory/rep_set.h"
#include "theory/substitutions.h"
#include "theory/type_enumerator.h"
#include "theory/type_set.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

/** Theory Model class.
 *
 * This class represents a model produced by the TheoryEngine.
 * The data structures used to represent a model are:
 * (1) d_equalityEngine : an equality engine object, which stores
 *     an equivalence relation over all terms that exist in
 *     the current set of assertions.
 * (2) d_substitutions : a substitution map storing cases of
 *     explicitly solved terms, for instance during preprocessing.
 * (3) d_reps : a map from equivalence class representatives of
 *     the equality engine to the (constant) representatives
 *     assigned to that equivalence class.
 * (4) d_uf_models : a map from uninterpreted functions to their
 *     lambda representation.
 * (5) d_rep_set : a data structure that allows interpretations
 *     for types to be represented as terms. This is useful for
 *     finite model finding.
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
class TheoryModel : public Model
{
  friend class TheoryEngineModelBuilder;
public:
  TheoryModel(context::Context* c, std::string name, bool enableFuncModels);
  ~TheoryModel() override;

  /** reset the model */
  virtual void reset();
  /** is built
   *
   * Have we attempted to build this model since the last
   * call to reset? Notice for model building techniques
   * that are not guaranteed to succeed (such as
   * when quantified formulas are enabled), a true return
   * value does not imply that this is a model of the
   * current assertions.
   */
  bool isBuilt() { return d_modelBuilt; }
  /** is built success
   *
   * Was this model successfully built since the last call to reset?
   */
  bool isBuiltSuccess() { return d_modelBuiltSuccess; }
  //---------------------------- for building the model
  /** Adds a substitution from x to t. */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);
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
                            std::set<Node>* termSet = NULL);
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
   *   useDontCares is whether to return Node::null() if
   *     n does not occur in the equality engine.
   */
  Node getValue(TNode n, bool useDontCares = false) const;
  /** get comments */
  void getComments(std::ostream& out) const override;

  //---------------------------- separation logic
  /** set the heap and value sep.nil is equal to */
  void setHeapModel(Node h, Node neq);
  /** get the heap and value sep.nil is equal to */
  bool getHeapModel(Expr& h, Expr& neq) const override;
  //---------------------------- end separation logic

  /** get the representative set object */
  const RepSet* getRepSet() const { return &d_rep_set; }
  /** get the representative set object (FIXME: remove this, see #1199) */
  RepSet* getRepSetPtr() { return &d_rep_set; }
  /** return whether this node is a don't-care */
  bool isDontCare(Expr expr) const override;
  /** get value function for Exprs. */
  Expr getValue(Expr expr) const override;
  /** get cardinality for sort */
  Cardinality getCardinality(Type t) const override;
  /** print representative debug function */
  void printRepresentativeDebug( const char* c, Node r );
  /** print representative function */
  void printRepresentative( std::ostream& out, Node r );

  //---------------------------- function values
  /** a map from functions f to a list of all APPLY_UF terms with operator f */
  std::map< Node, std::vector< Node > > d_uf_terms;
  /** a map from functions f to a list of all HO_APPLY terms with first argument f */
  std::map< Node, std::vector< Node > > d_ho_uf_terms;
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
 protected:
  /** substitution map for this model */
  SubstitutionMap d_substitutions;
  /** whether we have tried to build this model in the current context */
  bool d_modelBuilt;
  /** whether this model has been built successfully */
  bool d_modelBuiltSuccess;
  /** special local context for our equalityEngine so we can clear it
   * independently of search context */
  context::Context* d_eeContext;
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine* d_equalityEngine;
  /** map of representatives of equality engine to used representatives in
   * representative set */
  std::map<Node, Node> d_reps;
  /** stores set of representatives for each type */
  RepSet d_rep_set;
  /** true/false nodes */
  Node d_true;
  Node d_false;
  /** comment stream to include in printing */
  std::stringstream d_comment_str;
  /** Get model value function.
   *
   * This function is a helper function for getValue.
   *   hasBoundVars is whether n may contain bound variables
   *   useDontCares is whether to return Node::null() if
   *     n does not occur in the equality engine.
   */
  Node getModelValue(TNode n,
                     bool hasBoundVars = false,
                     bool useDontCares = false) const;
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
  mutable std::unordered_map<Node, Node, NodeHashFunction> d_modelCache;

  //---------------------------- separation logic
  /** the value of the heap */
  Node d_sep_heap;
  /** the value of the nil element */
  Node d_sep_nil_eq;
  //---------------------------- end separation logic

  //---------------------------- function values
  /** whether function models are enabled */
  bool d_enableFuncModels;
  /** map from function terms to the (lambda) definitions
  * After the model is built, the domain of this map is all terms of function
  * type that appear as terms in d_equalityEngine.
  */
  std::map<Node, Node> d_uf_models;
  //---------------------------- end function values
};/* class TheoryModel */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_MODEL_H */

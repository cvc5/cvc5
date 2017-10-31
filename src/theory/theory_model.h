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
#include "theory/uf/equality_engine.h"
#include "theory/rep_set.h"
#include "theory/substitutions.h"
#include "theory/type_enumerator.h"
#include "theory/type_set.h"

namespace CVC4 {
namespace theory {

/**
 * Theory Model class.
 *    For Model m, should call m.initialize() before using.
 */
class TheoryModel : public Model
{
  friend class TheoryEngineModelBuilder;

public:
  TheoryModel(context::Context* c, std::string name, bool enableFuncModels);
  virtual ~TheoryModel() throw();

  /** get comments */
  void getComments(std::ostream& out) const;
  /** is built */
  bool isBuilt() { return d_modelBuilt; }
  /** set need build */
  void setNeedsBuild() { d_modelBuilt = false; }
  /**
   * Get value function.  This should be called only after a ModelBuilder has called buildModel(...)
   * on this model.
   */
  Node getValue( TNode n, bool useDontCares = false ) const;

  //---------------------------- separation logic
  /** set the heap and value sep.nil is equal to */
  void setHeapModel(Node h, Node neq);
  /** get the heap and value sep.nil is equal to */
  bool getHeapModel(Expr& h, Expr& neq) const;
  //---------------------------- end separation logic

  /** Adds a substitution from x to t. */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);
  /** add term function
    *   addTerm( n ) will do any model-specific processing necessary for n,
    *   such as constraining the interpretation of uninterpreted functions,
    *   and adding n to the equality engine of this model
    */
  virtual void addTerm(TNode n);
  /** assert equality holds in the model */
  void assertEquality(TNode a, TNode b, bool polarity);
  /** assert predicate holds in the model */
  void assertPredicate(TNode a, bool polarity);
  /** assert all equalities/predicates in equality engine hold in the model */
  void assertEqualityEngine(const eq::EqualityEngine* ee, std::set<Node>* termSet = NULL);
  /** assert representative
    *  This function tells the model that n should be the representative of its equivalence class.
    *  It should be called during model generation, before final representatives are chosen.  In the
    *  case of TheoryEngineModelBuilder, it should be called during Theory's collectModelInfo( ... )
    *  functions.
    */
  void assertRepresentative(TNode n);

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

  /** get the representative set object */
  const RepSet* getRepSet() const { return &d_rep_set; }
  /** get the representative set object (FIXME: remove this, see #1199) */
  RepSet* getRepSetPtr() { return &d_rep_set; }
  /** return whether this node is a don't-care */
  bool isDontCare(Expr expr) const;
  /** get value function for Exprs. */
  Expr getValue( Expr expr ) const;
  /** get cardinality for sort */
  Cardinality getCardinality( Type t ) const;
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
  /** whether this model has been built */
  bool d_modelBuilt;
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
  mutable std::unordered_map<Node, Node, NodeHashFunction> d_modelCache;
  /** comment stream to include in printing */
  std::stringstream d_comment_str;
  /** reset the model */
  virtual void reset();
  /**
   * Get model value function.  This function is called by getValue
   */
  Node getModelValue(TNode n,
                     bool hasBoundVars = false,
                     bool useDontCares = false) const;

 private:
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
  * type
  * that appear as terms in d_equalityEngine.
  */
  std::map<Node, Node> d_uf_models;
  //---------------------------- end function values
};/* class TheoryModel */

/** TheoryEngineModelBuilder class
  *    This model builder will consult all theories in a theory engine for
  *    collectModelInfo( ... ) when building a model.
  */
class TheoryEngineModelBuilder : public ModelBuilder
{
protected:
  /** pointer to theory engine */
  TheoryEngine* d_te;
  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_normalizedCache;
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
  std::map< Node, Node > d_constantReps;

  /** process build model */
  virtual bool preProcessBuildModel(TheoryModel* m);
  virtual bool processBuildModel(TheoryModel* m);
  virtual void debugModel( TheoryModel* m ) {}
  /** normalize representative */
  Node normalize(TheoryModel* m, TNode r, bool evalOnly);
  bool isAssignable(TNode n);
  void checkTerms(TNode n, TheoryModel* tm, NodeSet& cache);
  void assignConstantRep( TheoryModel* tm, Node eqc, Node const_rep );
  void addToTypeList( TypeNode tn, std::vector< TypeNode >& type_list, std::map< TypeNode, bool >& visiting );
  /** is v an excluded codatatype value */
  bool isExcludedCdtValue( Node v, std::set<Node>* repSet, std::map< Node, Node >& assertedReps, Node eqc );
  bool isCdtValueMatch( Node v, Node r, Node eqc, Node& eqc_m );
  /** involves usort */
  bool involvesUSort( TypeNode tn );
  bool isExcludedUSortValue( std::map< TypeNode, unsigned >& eqc_usort_count, Node v, std::map< Node, bool >& visited );
protected:
  /** assign function f based on the model m. 
  * This construction is based on "table form". For example:
  * (f 0 1) = 1
  * (f 0 2) = 2
  * (f 1 1) = 3
  * ...
  * becomes:
  * f = (lambda xy. (ite (and (= x 0) (= y 1)) 1 
  *                 (ite (and (= x 0) (= y 2)) 2
  *                 (ite (and (= x 1) (= y 1)) 3 ...)))
  */
  void assignFunction(TheoryModel* m, Node f);
  /** assign function f based on the model m. 
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
  */
  void assignHoFunction(TheoryModel* m, Node f);
  /** Assign all unassigned functions in the model m (those returned by TheoryModel::getFunctionsToAssign), 
  * using the two functions above. Currently:
  * If ufHo is disabled, we call assignFunction for all functions. 
  * If ufHo is enabled, we call assignHoFunction.
  */
  void assignFunctions(TheoryModel* m);
public:
  TheoryEngineModelBuilder(TheoryEngine* te);
  virtual ~TheoryEngineModelBuilder(){}
  /** Build model function.
   *    Should be called only on TheoryModels m
   */
  bool buildModel(Model* m);
  void debugCheckModel(Model* m);
};/* class TheoryEngineModelBuilder */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_MODEL_H */

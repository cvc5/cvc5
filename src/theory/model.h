/*********************                                                        */
/*! \file model.h
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_MODEL_H
#define __CVC4__THEORY_MODEL_H

#include "util/model.h"
#include "theory/uf/equality_engine.h"
#include "theory/rep_set.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;
class TheoryEngineModelBuilder;

/** Theory Model class
 *    For Model m, should call m.initialize() before using
 */
class TheoryModel : public Model
{
  friend class TheoryEngineModelBuilder;
protected:
  /** add term function
    *   This should be called on all terms that exist in the model.
    *   addTerm( n ) will do any model-specific processing necessary for n,
    *   such as contraining the interpretation of uninterpretted functions.
    */
  virtual void addTerm( Node n ) {}
  /** substitution map for this model */
  SubstitutionMap d_substitutions;
public:
  TheoryModel( context::Context* c, std::string name );
  virtual ~TheoryModel(){}
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine d_equalityEngine;
  /** map of representatives of equality engine to used representatives in representative set */
  std::map< Node, Node > d_reps;
  /** stores set of representatives for each type */
  RepSet d_rep_set;
  /** true/false nodes */
  Node d_true;
  Node d_false;
protected:
  /** reset the model */
  virtual void reset();
  /** get interpreted value
    *  This function is called when the value of the node cannot be determined by the theory rewriter
    *  This should function should return a representative in d_reps
    */
  virtual Node getInterpretedValue( TNode n ) = 0;
  /**
   * Get model value function.  This function is called by getValue
   */
  Node getModelValue( TNode n );
public:
  /** get existing domain value, with possible exclusions
    *   This function returns a term in d_rep_set.d_type_reps[tn] but not in exclude
    */
  Node getDomainValue( TypeNode tn, std::vector< Node >& exclude );
  /** get new domain value
    *   This function returns a constant term of type tn that is not in d_rep_set.d_type_reps[tn]
    *   If it cannot find such a node, it returns null.
    */
  Node getNewDomainValue( TypeNode tn );
  /** complete all values for type
    *   Calling this function ensures that all terms of type tn exist in d_rep_set.d_type_reps[tn]
    */
  void completeDomainValues( TypeNode tn ){
    d_rep_set.complete( tn );
  }
public:
  /** Adds a substitution from x to t. */
  void addSubstitution(TNode x, TNode t, bool invalidateCache = true);
  /** assert equality holds in the model */
  void assertEquality( Node a, Node b, bool polarity );
  /** assert predicate holds in the model */
  void assertPredicate( Node a, bool polarity );
  /** assert all equalities/predicates in equality engine hold in the model */
  void assertEqualityEngine( const eq::EqualityEngine* ee );
  /** assert representative
    *  This function tells the model that n should be the representative of its equivalence class.
    *  It should be called during model generation, before final representatives are chosen.  In the
    *  case of TheoryEngineModelBuilder, it should be called during Theory's collectModelInfo( ... )
    *  functions where fullModel = true.
    */
  void assertRepresentative( Node n );
public:
  /** general queries */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
public:
  /** get value function */
  Expr getValue( const Expr& expr );
  /** to stream function */
  void toStream( std::ostream& out );
public:
  /** print representative debug function */
  void printRepresentativeDebug( const char* c, Node r );
  /** print representative function */
  void printRepresentative( std::ostream& out, Node r );
};

/** Default model class
  *   The getInterpretedValue function will choose an existing value arbitrarily.
  *   If none are found, then it will create a new value.
  */
class DefaultModel : public TheoryModel
{
protected:
  /** whether function models are enabled */
  bool d_enableFuncModels;
  /** add term */
  void addTerm( Node n );
public:
  DefaultModel( context::Context* c, std::string name, bool enableFuncModels );
  virtual ~DefaultModel(){}
  //necessary information for function models
  std::map< Node, std::vector< Node > > d_uf_terms;
  std::map< Node, Node > d_uf_models;
public:
  void reset();
  Node getInterpretedValue( TNode n );
};

/** TheoryEngineModelBuilder class
  *    This model builder will consult all theories in a theory engine for
  *    collectModelInfo( ... ) when building a model.
  */
class TheoryEngineModelBuilder : public ModelBuilder
{
protected:
  /** pointer to theory engine */
  TheoryEngine* d_te;
  /** process build model */
  virtual void processBuildModel( TheoryModel* m, bool fullModel ){}
  /** choose representative for unconstrained equivalence class */
  virtual Node chooseRepresentative( TheoryModel* m, Node eqc, bool fullModel );
  /** normalize representative */
  Node normalizeRepresentative( TheoryModel* m, Node r, std::map< Node, Node >& reps,
                                std::map< Node, bool >& normalized,
                                std::map< Node, bool >& normalizing );
  Node normalizeNode( TheoryModel* m, Node r, std::map< Node, Node >& reps,
                      std::map< Node, bool >& normalized,
                      std::map< Node, bool >& normalizing );
public:
  TheoryEngineModelBuilder( TheoryEngine* te );
  virtual ~TheoryEngineModelBuilder(){}
  /** Build model function.
   *    Should be called only on TheoryModels m
   */
  void buildModel( Model* m, bool fullModel );
};

}
}

#endif

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

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

/** this class stores a representative set */
class RepSet {
public:
  RepSet(){}
  ~RepSet(){}
  std::map< TypeNode, std::vector< Node > > d_type_reps;
  std::map< Node, int > d_tmap;
  /** clear the set */
  void clear();
  /** has type */
  bool hasType( TypeNode tn ) { return d_type_reps.find( tn )!=d_type_reps.end(); }
  /** add representative for type */
  void add( Node n );
  /** set the representatives for type */
  void set( TypeNode t, std::vector< Node >& reps );
  /** returns index in d_type_reps for node n */
  int getIndexFor( Node n ) { return d_tmap.find( n )!=d_tmap.end() ? d_tmap[n] : -1; }
  /** debug print */
  void toStream(std::ostream& out);
};

//representative domain
typedef std::vector< int > RepDomain;

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
private:
  /** List of definitions that the user has given
    *  This is necessary for supporting the get-model command.
    */
  std::vector< Node > d_define_funcs;
  std::vector< TypeNode > d_define_types;
  std::vector< int > d_defines;
protected:
  /** print the value of the function n to stream */
  virtual void toStreamFunction( Node n, std::ostream& out );
  /** print the value of the type tn to stream */
  virtual void toStreamType( TypeNode tn, std::ostream& out );
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
public:
  /** reset the model */
  virtual void reset();
  /** get interpreted value
    *  This function is called when the value of the node cannot be determined by the theory rewriter
    *  This should function should return a representative in d_reps
    */
  virtual Node getInterpretedValue( TNode n ) = 0;
public:
  /** add defined function (for get-model) */
  void addDefineFunction( Node n );
  /** add defined type (for get-model) */
  void addDefineType( TypeNode tn );
  /**
   * Get value function.  This should be called only after a ModelBuilder has called buildModel(...)
   * on this model.
   */
  Node getValue( TNode n );
  /** get existing domain value, with possible exclusions
    *   This function returns a term in d_rep_set.d_type_reps[tn] but not in exclude
    */
  Node getDomainValue( TypeNode tn, std::vector< Node >& exclude );
  /** get new domain value
    *   This function returns a constant term of type tn that is not in d_rep_set.d_type_reps[tn]
    *   If it cannot find such a node, it returns null.
    */
  Node getNewDomainValue( TypeNode tn );
public:
  /** assert equality holds in the model */
  void assertEquality( Node a, Node b, bool polarity );
  /** assert predicate holds in the model */
  void assertPredicate( Node a, bool polarity );
  /** assert all equalities/predicates in equality engine hold in the model */
  void assertEqualityEngine( eq::EqualityEngine* ee );
public:
  /** general queries */
  bool hasTerm( Node a );
  Node getRepresentative( Node a );
  bool areEqual( Node a, Node b );
  bool areDisequal( Node a, Node b );
public:
  /** print representative debug function */
  void printRepresentativeDebug( const char* c, Node r );
  /** print representative function */
  void printRepresentative( std::ostream& out, Node r );
  /** to stream function */
  void toStream( std::ostream& out );
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
  /** choose representative for unresolved equivalence class */
  void initializeType( TypeNode tn, std::map< TypeNode, bool >& unresolved_types );
  /** process build model */
  virtual void processBuildModel( TheoryModel* m ){}
  /** choose representative for unconstrained equivalence class */
  virtual Node chooseRepresentative( TheoryModel* m, Node eqc );
public:
  TheoryEngineModelBuilder( TheoryEngine* te );
  virtual ~TheoryEngineModelBuilder(){}
  /** Build model function.
   *    Should be called only on TheoryModels m
   */
  void buildModel( Model* m );
};

}
}

#endif

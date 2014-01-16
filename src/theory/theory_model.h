/*********************                                                        */
/*! \file theory_model.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds, Clark Barrett
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__THEORY_MODEL_H
#define __CVC4__THEORY__THEORY_MODEL_H

#include "util/model.h"
#include "theory/uf/equality_engine.h"
#include "theory/rep_set.h"
#include "theory/substitutions.h"
#include "theory/type_enumerator.h"

namespace CVC4 {
namespace theory {

/**
 * Theory Model class.
 *    For Model m, should call m.initialize() before using.
 */
class TheoryModel : public Model
{
  friend class TheoryEngineModelBuilder;
protected:
  /** substitution map for this model */
  SubstitutionMap d_substitutions;
public:
  TheoryModel(context::Context* c, std::string name, bool enableFuncModels);
  virtual ~TheoryModel(){}

  /** special local context for our equalityEngine so we can clear it independently of search context */
  context::Context* d_eeContext;
  /** equality engine containing all known equalities/disequalities */
  eq::EqualityEngine* d_equalityEngine;
  /** map of representatives of equality engine to used representatives in representative set */
  std::map< Node, Node > d_reps;
  /** stores set of representatives for each type */
  RepSet d_rep_set;
  /** true/false nodes */
  Node d_true;
  Node d_false;
  context::CDO<bool> d_modelBuilt;

protected:
  /** reset the model */
  virtual void reset();
  /**
   * Get model value function.  This function is called by getValue
   */
  Node getModelValue(TNode n, bool hasBoundVars = false) const;
public:
  /**
   * Get value function.  This should be called only after a ModelBuilder has called buildModel(...)
   * on this model.
   */
  Node getValue( TNode n ) const;

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
    *  functions where fullModel = true.
    */
  void assertRepresentative(TNode n);
public:
  /** general queries */
  bool hasTerm(TNode a);
  Node getRepresentative(TNode a);
  bool areEqual(TNode a, TNode b);
  bool areDisequal(TNode a, TNode b);
public:
  /** get value function for Exprs. */
  Expr getValue( Expr expr ) const;
  /** get cardinality for sort */
  Cardinality getCardinality( Type t ) const;
public:
  /** print representative debug function */
  void printRepresentativeDebug( const char* c, Node r );
  /** print representative function */
  void printRepresentative( std::ostream& out, Node r );
public:
  /** whether function models are enabled */
  bool d_enableFuncModels;
  //necessary information for function models
  std::map< Node, std::vector< Node > > d_uf_terms;
  std::map< Node, Node > d_uf_models;
};/* class TheoryModel */

/*
 * Class that encapsulates a map from types to sets of nodes
 */
class TypeSet {
public:
  typedef std::hash_map<TypeNode, std::set<Node>*, TypeNodeHashFunction> TypeSetMap;
  typedef std::hash_map<TypeNode, TypeEnumerator*, TypeNodeHashFunction> TypeToTypeEnumMap;
  typedef TypeSetMap::iterator iterator;
  typedef TypeSetMap::const_iterator const_iterator;
private:
  TypeSetMap d_typeSet;
  TypeToTypeEnumMap d_teMap;

  public:
  ~TypeSet() {
    iterator it;
    for (it = d_typeSet.begin(); it != d_typeSet.end(); ++it) {
      if ((*it).second != NULL) {
        delete (*it).second;
      }
    }
    TypeToTypeEnumMap::iterator it2;
    for (it2 = d_teMap.begin(); it2 != d_teMap.end(); ++it2) {
      if ((*it2).second != NULL) {
        delete (*it2).second;
      }
    }
  }

  void add(TypeNode t, TNode n)
  {
    iterator it = d_typeSet.find(t);
    std::set<Node>* s;
    if (it == d_typeSet.end()) {
      s = new std::set<Node>;
      d_typeSet[t] = s;
    }
    else {
      s = (*it).second;
    }
    s->insert(n);
  }

  std::set<Node>* getSet(TypeNode t) const
  {
    const_iterator it = d_typeSet.find(t);
    if (it == d_typeSet.end()) {
      return NULL;
    }
    return (*it).second;
  }

  Node nextTypeEnum(TypeNode t, bool useBaseType = false)
  {
    TypeEnumerator* te;
    TypeToTypeEnumMap::iterator it = d_teMap.find(t);
    if (it == d_teMap.end()) {
      te = new TypeEnumerator(t);
      d_teMap[t] = te;
    }
    else {
      te = (*it).second;
    }
    if (te->isFinished()) {
      return Node();
    }

    if (useBaseType) {
      t = t.getBaseType();
    }
    iterator itSet = d_typeSet.find(t);
    std::set<Node>* s;
    if (itSet == d_typeSet.end()) {
      s = new std::set<Node>;
      d_typeSet[t] = s;
    }
    else {
      s = (*itSet).second;
    }
    Node n = **te;
    while (s->find(n) != s->end()) {
      ++(*te);
      if (te->isFinished()) {
        return Node();
      }
      n = **te;
    }
    s->insert(n);
    ++(*te);
    return n;
  }

  bool empty()
  {
    return d_typeSet.empty();
  }

  iterator begin()
  {
    return d_typeSet.begin();
  }

  iterator end()
  {
    return d_typeSet.end();
  }

  static TypeNode getType(iterator it)
  {
    return (*it).first;
  }

  static std::set<Node>& getSet(iterator it)
  {
    return *(*it).second;
  }

};/* class TypeSet */

/** TheoryEngineModelBuilder class
  *    This model builder will consult all theories in a theory engine for
  *    collectModelInfo( ... ) when building a model.
  */
class TheoryEngineModelBuilder : public ModelBuilder
{
protected:
  /** pointer to theory engine */
  TheoryEngine* d_te;
  typedef std::hash_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_normalizedCache;
  typedef std::hash_set<Node, NodeHashFunction> NodeSet;

  /** process build model */
  virtual void processBuildModel(TheoryModel* m, bool fullModel);
  /** normalize representative */
  Node normalize(TheoryModel* m, TNode r, std::map<Node, Node>& constantReps, bool evalOnly);
  bool isAssignable(TNode n);
  void checkTerms(TNode n, TheoryModel* tm, NodeSet& cache);

public:
  TheoryEngineModelBuilder(TheoryEngine* te);
  virtual ~TheoryEngineModelBuilder(){}
  /** Build model function.
   *    Should be called only on TheoryModels m
   */
  void buildModel(Model* m, bool fullModel);
};/* class TheoryEngineModelBuilder */

}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__THEORY_MODEL_H */

/*********************                                                        */
/*! \file first_order_model.h
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Model extended classes
 **/

#include "cvc4_private.h"

#ifndef __CVC4__FIRST_ORDER_MODEL_H
#define __CVC4__FIRST_ORDER_MODEL_H

#include "theory/theory_model.h"
#include "theory/uf/theory_uf_model.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers{

class TermDb;

class FirstOrderModelIG;
namespace fmcheck {
  class FirstOrderModelFmc;
}

class FirstOrderModel : public TheoryModel
{
private:
  /** whether an axiom is asserted */
  context::CDO< bool > d_axiom_asserted;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** is model set */
  context::CDO< bool > d_isModelSet;
  /** get current model value */
  virtual Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial ) = 0;
public: //for Theory Quantifiers:
  /** assert quantifier */
  void assertQuantifier( Node n );
  /** get number of asserted quantifiers */
  int getNumAssertedQuantifiers() { return (int)d_forall_asserts.size(); }
  /** get asserted quantifier */
  Node getAssertedQuantifier( int i ) { return d_forall_asserts[i]; }
  /** bool axiom asserted */
  bool isAxiomAsserted() { return d_axiom_asserted; }
  /** initialize model for term */
  void initializeModelForTerm( Node n );
  virtual void processInitializeModelForTerm( Node n ) = 0;
public:
  FirstOrderModel( context::Context* c, std::string name );
  virtual ~FirstOrderModel(){}
  virtual FirstOrderModelIG * asFirstOrderModelIG() { return NULL; }
  virtual fmcheck::FirstOrderModelFmc * asFirstOrderModelFmc() { return NULL; }
  // initialize the model
  void initialize( bool considerAxioms = true );
  virtual void processInitialize() = 0;
  /** mark model set */
  void markModelSet() { d_isModelSet = true; }
  /** is model set */
  bool isModelSet() { return d_isModelSet; }
  /** get current model value */
  Node getCurrentModelValue( Node n, bool partial = false );
};/* class FirstOrderModel */


class FirstOrderModelIG : public FirstOrderModel
{
public: //for Theory UF:
  //models for each UF operator
  std::map< Node, uf::UfModelTree > d_uf_model_tree;
  //model generators
  std::map< Node, uf::UfModelTreeGenerator > d_uf_model_gen;
private:
  //map from terms to the models used to calculate their value
  std::map< Node, bool > d_eval_uf_use_default;
  std::map< Node, uf::UfModelTree > d_eval_uf_model;
  void makeEvalUfModel( Node n );
  //index ordering to use for each term
  std::map< Node, std::vector< int > > d_eval_term_index_order;
  void makeEvalUfIndexOrder( Node n );
  /** get current model value */
  Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial );
//the following functions are for evaluating quantifier bodies
public:
  FirstOrderModelIG(context::Context* c, std::string name);
  FirstOrderModelIG * asFirstOrderModelIG() { return this; }
  // initialize the model
  void processInitialize();
  //for initialize model
  void processInitializeModelForTerm( Node n );
  /** reset evaluation */
  void resetEvaluate();
  /** evaluate functions */
  int evaluate( Node n, int& depIndex, RepSetIterator* ri  );
  Node evaluateTerm( Node n, int& depIndex, RepSetIterator* ri  );
public:
  //statistics
  int d_eval_formulas;
  int d_eval_uf_terms;
  int d_eval_lits;
  int d_eval_lits_unknown;
private:
  //default evaluate term function
  Node evaluateTermDefault( Node n, int& depIndex, std::vector< int >& childDepIndex, RepSetIterator* ri  );
  //temporary storing which literals have failed
  void clearEvalFailed( int index );
  std::map< Node, bool > d_eval_failed;
  std::map< int, std::vector< Node > > d_eval_failed_lits;
};


namespace fmcheck {

class Def;

class FirstOrderModelFmc : public FirstOrderModel
{
  friend class FullModelChecker;
private:
  /** quant engine */
  QuantifiersEngine * d_qe;
  /** models for UF */
  std::map<Node, Def * > d_models;
  std::map<TypeNode, Node > d_model_basis_rep;
  std::map<TypeNode, Node > d_type_star;
  Node intervalOp;
  Node getUsedRepresentative(Node n, bool strict = false);
  /** get current model value */
  Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial );
  void processInitializeModelForTerm(Node n);
public:
  FirstOrderModelFmc(QuantifiersEngine * qe, context::Context* c, std::string name);
  FirstOrderModelFmc * asFirstOrderModelFmc() { return this; }
  // initialize the model
  void processInitialize();

  Node getFunctionValue(Node op, const char* argPrefix );

  bool isStar(Node n);
  Node getStar(TypeNode tn);
  Node getStarElement(TypeNode tn);
  bool isModelBasisTerm(Node n);
  Node getModelBasisTerm(TypeNode tn);
  Node getSomeDomainElement(TypeNode tn);
  bool isInterval(Node n);
  Node getInterval( Node lb, Node ub );
  bool isInRange( Node v, Node i );
};

}


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__FIRST_ORDER_MODEL_H */

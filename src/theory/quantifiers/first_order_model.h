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
#include "expr/attribute.h"

namespace CVC4 {
namespace theory {

class QuantifiersEngine;

namespace quantifiers{

class TermDb;

class FirstOrderModelIG;
namespace fmcheck {
  class FirstOrderModelFmc;
}
class FirstOrderModelQInt;

struct IsStarAttributeId {};
typedef expr::Attribute<IsStarAttributeId, bool> IsStarAttribute;

class FirstOrderModel : public TheoryModel
{
protected:
  /** quant engine */
  QuantifiersEngine * d_qe;
  /** whether an axiom is asserted */
  context::CDO< bool > d_axiom_asserted;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** is model set */
  context::CDO< bool > d_isModelSet;
  /** get variable id */
  std::map< Node, std::map< Node, int > > d_quant_var_id;
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
  virtual void processInitializeQuantifier( Node q ) {}
public:
  FirstOrderModel(QuantifiersEngine * qe, context::Context* c, std::string name );
  virtual ~FirstOrderModel(){}
  virtual FirstOrderModelIG * asFirstOrderModelIG() { return NULL; }
  virtual fmcheck::FirstOrderModelFmc * asFirstOrderModelFmc() { return NULL; }
  virtual FirstOrderModelQInt * asFirstOrderModelQInt() { return NULL; }
  // initialize the model
  void initialize( bool considerAxioms = true );
  virtual void processInitialize( bool ispre ) = 0;
  /** mark model set */
  void markModelSet() { d_isModelSet = true; }
  /** is model set */
  bool isModelSet() { return d_isModelSet; }
  /** get current model value */
  Node getCurrentModelValue( Node n, bool partial = false );
  /** get variable id */
  int getVariableId(Node f, Node n) {
    return d_quant_var_id.find( f )!=d_quant_var_id.end() ? d_quant_var_id[f][n] : -1;
  }
  /** get some domain element */
  Node getSomeDomainElement(TypeNode tn);
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
  FirstOrderModelIG(QuantifiersEngine * qe, context::Context* c, std::string name);
  FirstOrderModelIG * asFirstOrderModelIG() { return this; }
  // initialize the model
  void processInitialize( bool ispre );
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
  void processInitialize( bool ispre );
  Node getFunctionValue(Node op, const char* argPrefix );

  bool isStar(Node n);
  Node getStar(TypeNode tn);
  Node getStarElement(TypeNode tn);
  bool isModelBasisTerm(Node n);
  Node getModelBasisTerm(TypeNode tn);
  bool isInterval(Node n);
  Node getInterval( Node lb, Node ub );
  bool isInRange( Node v, Node i );
};

}


class QIntDef;
class QuantVarOrder;
class FirstOrderModelQInt : public FirstOrderModel
{
  friend class QIntervalBuilder;
private:
  /** uf op to some representation */
  std::map<Node, QIntDef * > d_models;
  /** representatives to ids */
  std::map< Node, int > d_rep_id;
  std::map< TypeNode, Node > d_min;
  std::map< TypeNode, Node > d_max;
  /** quantifiers to information regarding variable ordering */
  std::map<Node, QuantVarOrder * > d_var_order;
  /** get current model value */
  Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial );
  void processInitializeModelForTerm(Node n);
public:
  FirstOrderModelQInt(QuantifiersEngine * qe, context::Context* c, std::string name);
  FirstOrderModelQInt * asFirstOrderModelQInt() { return this; }
  void processInitialize( bool ispre );
  Node getFunctionValue(Node op, const char* argPrefix );

  Node getUsedRepresentative( Node n );
  int getRepId( Node n ) { return d_rep_id.find( n )==d_rep_id.end() ? -1 : d_rep_id[n]; }
  bool isLessThan( Node v1, Node v2 );
  Node getMin( Node v1, Node v2 );
  Node getMax( Node v1, Node v2 );
  Node getMinimum( TypeNode tn ) { return getNext( tn, Node::null() ); }
  Node getMaximum( TypeNode tn );
  bool isMinimum( Node n ) { return n==getMinimum( n.getType() ); }
  bool isMaximum( Node n ) { return n==getMaximum( n.getType() ); }
  Node getNext( TypeNode tn, Node v );
  Node getPrev( TypeNode tn, Node v );
  bool doMeet( Node l1, Node u1, Node l2, Node u2, Node& lr, Node& ur );
  QuantVarOrder * getVarOrder( Node q ) { return d_var_order[q]; }

  void processInitializeQuantifier( Node q ) ;
  unsigned getOrderedNumVars( Node q );
  TypeNode getOrderedVarType( Node q, int i );
  int getOrderedVarNumToVarNum( Node q, int i );
};


}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__FIRST_ORDER_MODEL_H */

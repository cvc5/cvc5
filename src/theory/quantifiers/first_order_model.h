/*********************                                                        */
/*! \file first_order_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
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

namespace quantifiers {

class TermDb;

class FirstOrderModelIG;

namespace fmcheck {
  class FirstOrderModelFmc;
}/* CVC4::theory::quantifiers::fmcheck namespace */

class FirstOrderModelQInt;
class FirstOrderModelAbs;

struct IsStarAttributeId {};
typedef expr::Attribute<IsStarAttributeId, bool> IsStarAttribute;

class FirstOrderModel : public TheoryModel
{
protected:
  /** quant engine */
  QuantifiersEngine * d_qe;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** quantified formulas marked as relevant */
  unsigned d_rlv_count;
  std::map< Node, unsigned > d_forall_rlv;
  std::vector< Node > d_forall_rlv_vec;
  Node d_last_forall_rlv;
  std::vector< Node > d_forall_rlv_assert;
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
  unsigned getNumAssertedQuantifiers();
  /** get asserted quantifier */
  Node getAssertedQuantifier( unsigned i, bool ordered = false );
  /** initialize model for term */
  void initializeModelForTerm( Node n, std::map< Node, bool >& visited );
  virtual void processInitializeModelForTerm( Node n ) = 0;
  virtual void processInitializeQuantifier( Node q ) {}
public:
  FirstOrderModel(QuantifiersEngine * qe, context::Context* c, std::string name );
  virtual ~FirstOrderModel() throw() {}
  virtual FirstOrderModelIG * asFirstOrderModelIG() { return NULL; }
  virtual fmcheck::FirstOrderModelFmc * asFirstOrderModelFmc() { return NULL; }
  virtual FirstOrderModelQInt * asFirstOrderModelQInt() { return NULL; }
  virtual FirstOrderModelAbs * asFirstOrderModelAbs() { return NULL; }
  // initialize the model
  void initialize();
  virtual void processInitialize( bool ispre ) = 0;
  /** mark model set */
  void markModelSet() { d_isModelSet = true; }
  /** is model set */
  bool isModelSet() { return d_isModelSet; }
  /** get current model value */
  Node getCurrentModelValue( Node n, bool partial = false );
  /** get variable id */
  int getVariableId(TNode q, TNode n) {
    return d_quant_var_id.find( q )!=d_quant_var_id.end() ? d_quant_var_id[q][n] : -1;
  }
  /** get some domain element */
  Node getSomeDomainElement(TypeNode tn);
  /** do we need to do any work? */
  bool checkNeeded();
private:
  //list of inactive quantified formulas
  std::map< TNode, bool > d_quant_active;
public:
  /** reset round */
  void reset_round();
  /** mark quantified formula relevant */
  void markRelevant( Node q );
  /** get relevance value */
  int getRelevanceValue( Node q );
  /** set quantified formula active/inactive 
   * a quantified formula may be set inactive if for instance:
   *   - it is entailed by other quantified formulas
   */
  void setQuantifierActive( TNode q, bool active );
  /** is quantified formula active */
  bool isQuantifierActive( TNode q );
  /** is quantified formula asserted */
  bool isQuantifierAsserted( TNode q );
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
  ~FirstOrderModelIG() throw() {}
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
};/* class FirstOrderModelIG */


namespace fmcheck {

class Def;

class FirstOrderModelFmc : public FirstOrderModel
{
  friend class FullModelChecker;
private:
  /** models for UF */
  std::map<Node, Def * > d_models;
  std::map<TypeNode, Node > d_type_star;
  Node intervalOp;
  Node getUsedRepresentative(Node n, bool strict = false);
  /** get current model value */
  Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial );
  void processInitializeModelForTerm(Node n);
public:
  FirstOrderModelFmc(QuantifiersEngine * qe, context::Context* c, std::string name);
  virtual ~FirstOrderModelFmc() throw();
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
};/* class FirstOrderModelFmc */

}/* CVC4::theory::quantifiers::fmcheck namespace */

class AbsDef;

class FirstOrderModelAbs : public FirstOrderModel
{
public:
  std::map< Node, AbsDef * > d_models;
  std::map< Node, bool > d_models_valid;
  std::map< TNode, unsigned > d_rep_id;
  std::map< TypeNode, unsigned > d_domain;
  std::map< Node, std::vector< int > > d_var_order;
  std::map< Node, std::map< int, int > > d_var_index;
private:
  /** get current model value */
  Node getCurrentUfModelValue( Node n, std::vector< Node > & args, bool partial );
  void processInitializeModelForTerm(Node n);
  void processInitializeQuantifier( Node q );
  void collectEqVars( TNode q, TNode n, std::map< int, bool >& eq_vars );
public:
  FirstOrderModelAbs(QuantifiersEngine * qe, context::Context* c, std::string name);
  ~FirstOrderModelAbs() throw();
  FirstOrderModelAbs * asFirstOrderModelAbs() { return this; }
  void processInitialize( bool ispre );
  unsigned getRepresentativeId( TNode n );
  TNode getUsedRepresentative( TNode n );
  bool isValidType( TypeNode tn ) { return d_domain.find( tn )!=d_domain.end(); }
  Node getFunctionValue(Node op, const char* argPrefix );
  Node getVariable( Node q, unsigned i );
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__FIRST_ORDER_MODEL_H */

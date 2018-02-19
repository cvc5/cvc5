/*********************                                                        */
/*! \file first_order_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
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

struct ModelBasisAttributeId
{
};
typedef expr::Attribute<ModelBasisAttributeId, bool> ModelBasisAttribute;
// for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                     0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId
{
};
typedef expr::Attribute<ModelBasisArgAttributeId, uint64_t>
    ModelBasisArgAttribute;

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

/** Quantifiers representative bound
 *
 * This class is used for computing (finite)
 * bounds for the domain of a quantifier
 * in the context of a RepSetIterator
 * (see theory/rep_set.h).
 */
class QRepBoundExt : public RepBoundExt
{
 public:
  QRepBoundExt(QuantifiersEngine* qe) : d_qe(qe) {}
  virtual ~QRepBoundExt() {}
  /** set bound */
  virtual RepSetIterator::RsiEnumType setBound(
      Node owner, unsigned i, std::vector<Node>& elements) override;
  /** reset index */
  virtual bool resetIndex(RepSetIterator* rsi,
                          Node owner,
                          unsigned i,
                          bool initial,
                          std::vector<Node>& elements) override;
  /** initialize representative set for type */
  virtual bool initializeRepresentativesForType(TypeNode tn) override;
  /** get variable order */
  virtual bool getVariableOrder(Node owner,
                                std::vector<unsigned>& varOrder) override;

 private:
  /** quantifiers engine associated with this bound */
  QuantifiersEngine* d_qe;
  /** indices that are bound integer enumeration */
  std::map<unsigned, bool> d_bound_int;
};

// TODO (#1301) : document and refactor this class
class FirstOrderModel : public TheoryModel
{
 public:
  FirstOrderModel(QuantifiersEngine* qe, context::Context* c, std::string name);

  virtual FirstOrderModelIG* asFirstOrderModelIG() { return nullptr; }
  virtual fmcheck::FirstOrderModelFmc* asFirstOrderModelFmc() { return nullptr; }
  virtual FirstOrderModelQInt* asFirstOrderModelQInt() { return nullptr; }
  virtual FirstOrderModelAbs* asFirstOrderModelAbs() { return nullptr; }
  /** assert quantifier */
  void assertQuantifier( Node n );
  /** get number of asserted quantifiers */
  unsigned getNumAssertedQuantifiers();
  /** get asserted quantifier */
  Node getAssertedQuantifier( unsigned i, bool ordered = false );
  /** initialize model for term */
  void initializeModelForTerm( Node n, std::map< Node, bool >& visited );
  // initialize the model
  void initialize();
  /** get variable id */
  int getVariableId(TNode q, TNode n) {
    return d_quant_var_id.find( q )!=d_quant_var_id.end() ? d_quant_var_id[q][n] : -1;
  }
  /** do we need to do any work? */
  bool checkNeeded();
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
  /** get model basis term */
  Node getModelBasisTerm(TypeNode tn);
  /** is model basis term */
  bool isModelBasisTerm(Node n);
  /** get model basis term for op */
  Node getModelBasisOpTerm(Node op);
  /** get model basis */
  Node getModelBasis(Node q, Node n);
  /** get model basis body */
  Node getModelBasisBody(Node q);
  /** get model basis arg */
  unsigned getModelBasisArg(Node n);
  /** get some domain element */
  Node getSomeDomainElement(TypeNode tn);
  /** initialize representative set for type
   *
   * This ensures that TheoryModel::d_rep_set
   * is initialized for type tn. In particular:
   * (1) If tn is an uninitialized (unconstrained)
   * uninterpreted sort, then we interpret it
   * as a set of size one,
   * (2) If tn is a "small" enumerable finite type,
   * then we ensure that all its values are in
   * TheoryModel::d_rep_set.
   *
   * Returns true if the initialization was complete,
   * in that the set for tn in TheoryModel::d_rep_set
   * has all representatives of type tn.
   */
  bool initializeRepresentativesForType(TypeNode tn);

 protected:
  /** quant engine */
  QuantifiersEngine* d_qe;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** quantified formulas marked as relevant */
  unsigned d_rlv_count;
  std::map<Node, unsigned> d_forall_rlv;
  std::vector<Node> d_forall_rlv_vec;
  Node d_last_forall_rlv;
  std::vector<Node> d_forall_rlv_assert;
  /** get variable id */
  std::map<Node, std::map<Node, int> > d_quant_var_id;
  /** process initialize model for term */
  virtual void processInitializeModelForTerm(Node n) = 0;
  /** process intialize quantifier */
  virtual void processInitializeQuantifier(Node q) {}
  /** process initialize */
  virtual void processInitialize(bool ispre) = 0;

 private:
  // list of inactive quantified formulas
  std::map<TNode, bool> d_quant_active;
  /** map from types to model basis terms */
  std::map<TypeNode, Node> d_model_basis_term;
  /** map from ops to model basis terms */
  std::map<Node, Node> d_model_basis_op_term;
  /** map from instantiation terms to their model basis equivalent */
  std::map<Node, Node> d_model_basis_body;
  /** map from universal quantifiers to model basis terms */
  std::map<Node, std::vector<Node> > d_model_basis_terms;
  /** compute model basis arg */
  void computeModelBasisArgAttribute(Node n);
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
  /** get current model value */
  void processInitializeModelForTerm(Node n) override;

 public:
  FirstOrderModelFmc(QuantifiersEngine * qe, context::Context* c, std::string name);
  ~FirstOrderModelFmc() override;
  FirstOrderModelFmc* asFirstOrderModelFmc() override { return this; }
  // initialize the model
  void processInitialize(bool ispre) override;
  Node getFunctionValue(Node op, const char* argPrefix );

  bool isStar(Node n);
  Node getStar(TypeNode tn);
  Node getStarElement(TypeNode tn);
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
  void processInitializeModelForTerm(Node n) override;
  void processInitializeQuantifier(Node q) override;
  void collectEqVars( TNode q, TNode n, std::map< int, bool >& eq_vars );
  TNode getUsedRepresentative( TNode n );

 public:
  FirstOrderModelAbs(QuantifiersEngine * qe, context::Context* c, std::string name);
  ~FirstOrderModelAbs() override;
  FirstOrderModelAbs* asFirstOrderModelAbs() override { return this; }
  void processInitialize(bool ispre) override;
  unsigned getRepresentativeId( TNode n );
  bool isValidType( TypeNode tn ) { return d_domain.find( tn )!=d_domain.end(); }
  Node getFunctionValue(Node op, const char* argPrefix );
  Node getVariable( Node q, unsigned i );
};

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__FIRST_ORDER_MODEL_H */

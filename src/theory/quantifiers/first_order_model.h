/*********************                                                        */
/*! \file first_order_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model extended classes
 **/

#include "cvc4_private.h"

#ifndef CVC4__FIRST_ORDER_MODEL_H
#define CVC4__FIRST_ORDER_MODEL_H

#include "expr/attribute.h"
#include "theory/theory_model.h"
#include "theory/uf/theory_uf_model.h"

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

namespace fmcheck {
  class FirstOrderModelFmc;
}/* CVC4::theory::quantifiers::fmcheck namespace */

struct IsStarAttributeId {};
typedef expr::Attribute<IsStarAttributeId, bool> IsStarAttribute;

// TODO (#1301) : document and refactor this class
class FirstOrderModel : public TheoryModel
{
 public:
  FirstOrderModel(QuantifiersEngine* qe, context::Context* c, std::string name);

  virtual fmcheck::FirstOrderModelFmc* asFirstOrderModelFmc() { return nullptr; }
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
  /** set quantified formula active/inactive
   *
   * This indicates that quantified formula is "inactive", that is, it need
   * not be considered during this instantiation round.
   *
   * A quantified formula may be set inactive if for instance:
   *   - It is entailed by other quantified formulas, or
   *   - All of its instances are known to be true in the current model.
   *
   * This method should be called after a call to FirstOrderModel::reset_round,
   * and before calls to QuantifiersModule check calls. A common place to call
   * this method is during QuantifiersModule reset_round calls.
   */
  void setQuantifierActive( TNode q, bool active );
  /** is quantified formula active?
   *
   * Returns false if there has been a call to setQuantifierActive( q, false )
   * during this instantiation round.
   */
  bool isQuantifierActive(TNode q) const;
  /** is quantified formula asserted */
  bool isQuantifierAsserted(TNode q) const;
  /** get model basis term */
  Node getModelBasisTerm(TypeNode tn);
  /** is model basis term */
  bool isModelBasisTerm(Node n);
  /** get model basis term for op */
  Node getModelBasisOpTerm(Node op);
  /** get model basis */
  Node getModelBasis(Node q, Node n);
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
  std::vector<Node> d_forall_rlv_vec;
  Node d_last_forall_rlv;
  std::vector<Node> d_forall_rlv_assert;
  /** get variable id */
  std::map<Node, std::map<Node, int> > d_quant_var_id;
  /** process initialize model for term */
  virtual void processInitializeModelForTerm(Node n) {}
  /** process initialize quantifier */
  virtual void processInitializeQuantifier(Node q) {}
  /** process initialize */
  virtual void processInitialize(bool ispre) {}

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

namespace fmcheck {

class Def;

class FirstOrderModelFmc : public FirstOrderModel
{
  friend class FullModelChecker;

 private:
  /** models for UF */
  std::map<Node, Def * > d_models;
  std::map<TypeNode, Node > d_type_star;
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
};/* class FirstOrderModelFmc */

}/* CVC4::theory::quantifiers::fmcheck namespace */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__FIRST_ORDER_MODEL_H */

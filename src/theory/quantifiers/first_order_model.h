/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Paul Meng, Clark Barrett
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model extended classes.
 */

#include "cvc5_private.h"

#ifndef CVC5__FIRST_ORDER_MODEL_H
#define CVC5__FIRST_ORDER_MODEL_H

#include "context/cdlist.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/equality_query.h"
#include "theory/theory_model.h"
#include "theory/uf/theory_uf_model.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;
class RepSet;

namespace quantifiers {

class QuantifiersState;
class TermRegistry;
class QuantifiersRegistry;

// TODO (#1301) : document and refactor this class
class FirstOrderModel : protected EnvObj
{
 public:
  FirstOrderModel(Env& env,
                  QuantifiersState& qs,
                  QuantifiersRegistry& qr,
                  TermRegistry& tr);
  virtual ~FirstOrderModel() {}

  /** finish init */
  void finishInit(TheoryModel* m);
  //---------------------------------- access functions for underlying model
  /** Get value in the underlying theory model */
  Node getValue(TNode n) const;
  /** does the equality engine of this model have term a? */
  bool hasTerm(TNode a);
  /** get the representative of a in the equality engine of this model */
  Node getRepresentative(TNode a);
  /** are a and b equal in the equality engine of this model? */
  bool areEqual(TNode a, TNode b);
  /** are a and b disequal in the equality engine of this model? */
  bool areDisequal(TNode a, TNode b);
  /** get the equality engine for this model */
  eq::EqualityEngine* getEqualityEngine();
  /** get the representative set object */
  const RepSet* getRepSet() const;
  /** get the representative set object */
  RepSet* getRepSetPtr();
  /** get the entire theory model */
  TheoryModel* getTheoryModel();
  //---------------------------------- end access functions for underlying model
  /** get internal representative
   *
   * Choose a term that is equivalent to a in the current context that is the
   * best term for instantiating the index^th variable of quantified formula q.
   * If no legal term can be found, we return null. This can occur if:
   * - a's type is not the type of the index^th variable of q,
   * - a is in an equivalent class with all terms that are restricted not to
   * appear in instantiations of q, e.g. INST_CONSTANT terms for counterexample
   * guided instantiation.
   */
  Node getInternalRepresentative(Node a, Node q, size_t index);

  /** assert quantifier */
  void assertQuantifier( Node n );
  /** get number of asserted quantifiers */
  size_t getNumAssertedQuantifiers() const;
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
  /**
   * Has the term been marked as a model basis term?
   */
  static bool isModelBasis(TNode n);
  /** Get the equality query */
  EqualityQuery* getEqualityQuery();

 protected:
  /** Pointer to the underyling theory model */
  TheoryModel* d_model;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** equality query class */
  EqualityQuery d_eq_query;
  /** list of quantifiers asserted in the current context */
  context::CDList<Node> d_forall_asserts;
  /** 
   * The (ordered) list of quantified formulas marked as relevant using
   * markRelevant, where the quantified formula q in the most recent
   * call to markRelevant comes last in the list.
   */
  std::vector<Node> d_forall_rlv_vec;
  /** The last quantified formula marked as relevant, if one exists. */
  Node d_last_forall_rlv;
  /** 
   * The list of asserted quantified formulas, ordered by relevance.
   * Relevance is a dynamic partial ordering where q1 < q2 if there has been
   * a call to markRelevant( q1 ) after the last call to markRelevant( q2 )
   * (or no call to markRelevant( q2 ) has been made). 
   * 
   * This list is used primarily as an optimization for conflict-based
   * instantiation so that quantifed formulas that have been instantiated
   * most recently are processed first, since these are (statistically) more
   * likely to have conflicting instantiations.
   */
  std::vector<Node> d_forall_rlv_assert;
  /** 
   * Whether the above list has been computed. This flag is updated during
   * reset_round and is valid within a full effort check.
   */
  bool d_forallRlvComputed;
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__FIRST_ORDER_MODEL_H */

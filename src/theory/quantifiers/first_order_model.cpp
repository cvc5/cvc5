/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of model engine model class.
 */

#include "theory/quantifiers/first_order_model.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

struct ModelBasisAttributeId
{
};
using ModelBasisAttribute = expr::Attribute<ModelBasisAttributeId, bool>;
// for APPLY_UF terms, 1 : term has direct child with model basis attribute,
//                     0 : term has no direct child with model basis attribute.
struct ModelBasisArgAttributeId
{
};
using ModelBasisArgAttribute = expr::Attribute<ModelBasisArgAttributeId, uint64_t>;

FirstOrderModel::FirstOrderModel(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : EnvObj(env),
      d_model(nullptr),
      d_qreg(qr),
      d_treg(tr),
      d_eq_query(env, qs, this),
      d_forall_asserts(context()),
      d_forallRlvComputed(false)
{
}

void FirstOrderModel::finishInit(TheoryModel* m) { d_model = m; }

Node FirstOrderModel::getValue(TNode n) const { return d_model->getValue(n); }
bool FirstOrderModel::hasTerm(TNode a) { return d_model->hasTerm(a); }
Node FirstOrderModel::getRepresentative(TNode a)
{
  return d_model->getRepresentative(a);
}
bool FirstOrderModel::areEqual(TNode a, TNode b)
{
  return d_model->areEqual(a, b);
}
bool FirstOrderModel::areDisequal(TNode a, TNode b)
{
  return d_model->areDisequal(a, b);
}
eq::EqualityEngine* FirstOrderModel::getEqualityEngine()
{
  return d_model->getEqualityEngine();
}
const RepSet* FirstOrderModel::getRepSet() const
{
  return d_model->getRepSet();
}
RepSet* FirstOrderModel::getRepSetPtr() { return d_model->getRepSetPtr(); }
TheoryModel* FirstOrderModel::getTheoryModel() { return d_model; }

Node FirstOrderModel::getInternalRepresentative(Node a, Node q, size_t index)
{
  return d_eq_query.getInternalRepresentative(a, q, index);
}

void FirstOrderModel::assertQuantifier( Node n ){
  if( n.getKind()==FORALL ){
    d_forall_asserts.push_back( n );
  }else if( n.getKind()==NOT ){
    Assert(n[0].getKind() == FORALL);
  }
}

size_t FirstOrderModel::getNumAssertedQuantifiers() const
{
  return d_forall_asserts.size(); 
}

Node FirstOrderModel::getAssertedQuantifier( unsigned i, bool ordered ) { 
  if( !ordered || !d_forallRlvComputed ){
    return d_forall_asserts[i]; 
  }
  // If we computed the relevant forall assertion vector, in reset_round,
  // then it should have the same size as the default assertion vector.
  Assert(d_forall_rlv_assert.size() == d_forall_asserts.size());
  return d_forall_rlv_assert[i];
}

void FirstOrderModel::initialize() {
  processInitialize( true );
  //this is called after representatives have been chosen and the equality engine has been built
  //for each quantifier, collect all operators we care about
  for( unsigned i=0; i<getNumAssertedQuantifiers(); i++ ){
    Node f = getAssertedQuantifier( i );
    if( d_quant_var_id.find( f )==d_quant_var_id.end() ){
      for(unsigned j=0; j<f[0].getNumChildren(); j++){
        d_quant_var_id[f][f[0][j]] = j;
      }
    }
    processInitializeQuantifier( f );
    //initialize relevant models within bodies of all quantifiers
    std::map< Node, bool > visited;
    initializeModelForTerm( f[1], visited );
  }
  processInitialize( false );
}

void FirstOrderModel::initializeModelForTerm( Node n, std::map< Node, bool >& visited ){
  if( visited.find( n )==visited.end() ){
    visited[n] = true;
    processInitializeModelForTerm( n );
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      initializeModelForTerm( n[i], visited );
    }
  }
}

Node FirstOrderModel::getSomeDomainElement(TypeNode tn){
  //check if there is even any domain elements at all
  RepSet* rs = d_model->getRepSetPtr();
  if (!rs->hasType(tn) || rs->getNumRepresentatives(tn) == 0)
  {
    Trace("fm-debug") << "Must create domain element for " << tn << "..."
                      << std::endl;
    Node mbt = getModelBasisTerm(tn);
    Trace("fm-debug") << "Add to representative set..." << std::endl;
    rs->add(tn, mbt);
  }
  return rs->getRepresentative(tn, 0);
}

bool FirstOrderModel::initializeRepresentativesForType(TypeNode tn)
{
  RepSet* rs = d_model->getRepSetPtr();
  if (tn.isUninterpretedSort())
  {
    // must ensure uninterpreted type is non-empty.
    if (!rs->hasType(tn))
    {
      // terms in rep_set are now constants which mapped to terms through
      // TheoryModel. Thus, should introduce a constant and a term.
      // For now, we just add an arbitrary term.
      Node var = getSomeDomainElement(tn);
      Trace("mkVar") << "RepSetIterator:: Make variable " << var << " : " << tn
                     << std::endl;
      rs->add(tn, var);
    }
    return true;
  }
  else
  {
    // can we complete it?
    if (d_qreg.getQuantifiersBoundInference().mayComplete(tn))
    {
      Trace("fm-debug") << "  do complete, since cardinality is small"
                        << std::endl;
      rs->complete(tn);
      // must have succeeded
      Assert(rs->hasType(tn));
      return true;
    }
    Trace("fm-debug") << "  variable cannot be bounded." << std::endl;
    return false;
  }
}

bool FirstOrderModel::isModelBasis(TNode n)
{
  return n.getAttribute(ModelBasisAttribute());
}

EqualityQuery* FirstOrderModel::getEqualityQuery() { return &d_eq_query; }

/** needs check */
bool FirstOrderModel::checkNeeded() {
  return d_forall_asserts.size()>0;
}

void FirstOrderModel::reset_round() {
  d_quant_active.clear();

  // compute which quantified formulas are asserted if necessary
  std::map<Node, bool> qassert;
  if (!d_forall_rlv_vec.empty())
  {
    Trace("fm-relevant-debug")
        << "Mark asserted quantified formulas..." << std::endl;
    for (const Node& q : d_forall_asserts)
    {
      qassert[q] = true;
    }
  }
  //order the quantified formulas
  d_forall_rlv_assert.clear();
  d_forallRlvComputed = false;
  if( !d_forall_rlv_vec.empty() ){
    d_forallRlvComputed = true;
    Trace("fm-relevant") << "Build sorted relevant list..." << std::endl;
    Trace("fm-relevant-debug") << "Add relevant asserted formulas..." << std::endl;
    std::map<Node, bool>::iterator ita;
    for( int i=(int)(d_forall_rlv_vec.size()-1); i>=0; i-- ){
      Node q = d_forall_rlv_vec[i];
      ita = qassert.find(q);
      if (ita != qassert.end())
      {
        Trace("fm-relevant") << "   " << q << std::endl;
        d_forall_rlv_assert.push_back( q );
        qassert.erase(ita);
      }
    }
    Trace("fm-relevant-debug") << "Add remaining asserted formulas..." << std::endl;
    for (const Node& q : d_forall_asserts)
    {
      // if we didn't include it above
      if (qassert.find(q) != qassert.end())
      {
        d_forall_rlv_assert.push_back( q );
      }else{
        Trace("fm-relevant-debug") << "...already included " << q << std::endl;
      }
    }
    Trace("fm-relevant-debug") << "Sizes : " << d_forall_rlv_assert.size() << " " << d_forall_asserts.size() << std::endl;
    Assert(d_forall_rlv_assert.size() == d_forall_asserts.size());
  }
}

void FirstOrderModel::markRelevant( Node q ) {
  // Put q on the back of the vector d_forall_rlv_vec.
  // If we were the last quantifier marked relevant, this is a no-op, return.
  if( q!=d_last_forall_rlv ){
    Trace("fm-relevant") << "Mark relevant : " << q << std::endl;
    std::vector<Node>::iterator itr =
        std::find(d_forall_rlv_vec.begin(), d_forall_rlv_vec.end(), q);
    if (itr != d_forall_rlv_vec.end())
    {
      d_forall_rlv_vec.erase(itr, itr + 1);
    }
    d_forall_rlv_vec.push_back(q);
    d_last_forall_rlv = q;
  }
}

void FirstOrderModel::setQuantifierActive( TNode q, bool active ) {
  d_quant_active[q] = active;
}

bool FirstOrderModel::isQuantifierActive(TNode q) const
{
  std::map<TNode, bool>::const_iterator it = d_quant_active.find(q);
  if( it==d_quant_active.end() ){
    return true;
  }
  return it->second;
}

bool FirstOrderModel::isQuantifierAsserted(TNode q) const
{
  return std::find( d_forall_asserts.begin(), d_forall_asserts.end(), q )!=d_forall_asserts.end();
}

Node FirstOrderModel::getModelBasisTerm(TypeNode tn)
{
  if (d_model_basis_term.find(tn) == d_model_basis_term.end())
  {
    Node mbt;
    if (tn.isClosedEnumerable())
    {
      mbt = d_treg.getTermEnumeration()->getEnumerateTerm(tn, 0);
    }
    else
    {
      // The model basis term cannot be an interpreted function, or else we
      // may produce an inconsistent model by choosing an arbitrary
      // equivalence class for it. Hence, we require that it be an existing or
      // fresh variable.
      mbt = d_treg.getTermDatabase()->getOrMakeTypeGroundTerm(tn, true);
    }
    ModelBasisAttribute mba;
    mbt.setAttribute(mba, true);
    d_model_basis_term[tn] = mbt;
    Trace("model-basis-term") << "Choose " << mbt << " as model basis term for "
                              << tn << std::endl;
  }
  return d_model_basis_term[tn];
}

bool FirstOrderModel::isModelBasisTerm(Node n)
{
  return n == getModelBasisTerm(n.getType());
}

Node FirstOrderModel::getModelBasisOpTerm(Node op)
{
  if (d_model_basis_op_term.find(op) == d_model_basis_op_term.end())
  {
    TypeNode t = op.getType();
    std::vector<Node> children;
    children.push_back(op);
    for (int i = 0; i < (int)(t.getNumChildren() - 1); i++)
    {
      children.push_back(getModelBasisTerm(t[i]));
    }
    if (children.size() == 1)
    {
      d_model_basis_op_term[op] = op;
    }
    else
    {
      d_model_basis_op_term[op] =
          NodeManager::currentNM()->mkNode(APPLY_UF, children);
    }
  }
  return d_model_basis_op_term[op];
}

Node FirstOrderModel::getModelBasis(Node q, Node n)
{
  // make model basis
  if (d_model_basis_terms.find(q) == d_model_basis_terms.end())
  {
    for (unsigned j = 0; j < q[0].getNumChildren(); j++)
    {
      d_model_basis_terms[q].push_back(getModelBasisTerm(q[0][j].getType()));
    }
  }
  Node gn = d_qreg.substituteInstConstants(n, q, d_model_basis_terms[q]);
  return gn;
}

void FirstOrderModel::computeModelBasisArgAttribute(Node n)
{
  if (!n.hasAttribute(ModelBasisArgAttribute()))
  {
    // ensure that the model basis terms have been defined
    if (n.getKind() == APPLY_UF)
    {
      getModelBasisOpTerm(n.getOperator());
    }
    uint64_t val = 0;
    // determine if it has model basis attribute
    for (unsigned j = 0, nchild = n.getNumChildren(); j < nchild; j++)
    {
      if (n[j].getAttribute(ModelBasisAttribute()))
      {
        val++;
      }
    }
    ModelBasisArgAttribute mbaa;
    n.setAttribute(mbaa, val);
  }
}

unsigned FirstOrderModel::getModelBasisArg(Node n)
{
  computeModelBasisArgAttribute(n);
  return n.getAttribute(ModelBasisArgAttribute());
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

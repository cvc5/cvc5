/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of dynamic quantifiers splitting.
 */

#include "theory/quantifiers/quant_split.h"

#include "expr/bound_var_manager.h"
#include "expr/dtype.h"
#include "expr/dtype_cons.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "theory/datatypes/theory_datatypes_utils.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * A proof generator for quantifiers splitting inferences
 */
class QuantDSplitProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  QuantDSplitProofGenerator(Env& env) : EnvObj(env), d_index(userContext()) {}
  virtual ~QuantDSplitProofGenerator() {}
  /**
   * Get proof for fact. This expects facts of the form
   *    q = QuantDSplit::split(nm, q, n)
   * We prove this by:
   *    ------ QUANT_VAR_REORDERING ---------------------------- QUANT_DT_SPLIT
   *    q = q'                      q' = QuantDSplit::split(nm, q', 0)
   *    --------------------------------------------------------------- TRANS
   *    q = QuantDSplit::split(nm, q, n)
   *
   * where the variables in q' is reordered from q such that the variable to
   * split comes first.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override
  {
    CDProof cdp(d_env);
    // find the index of the variable that was split for this lemma
    context::CDHashMap<Node, size_t>::iterator it = d_index.find(fact);
    if (it == d_index.end())
    {
      Assert(false) << "QuantDSplitProofGenerator failed to get proof";
      return nullptr;
    }
    Assert(fact.getKind() == Kind::EQUAL && fact[0].getKind() == Kind::FORALL);
    Node q = fact[0];
    std::vector<Node> transEq;
    if (it->second != 0)
    {
      // must reorder variables
      std::vector<Node> newVars;
      newVars.push_back(q[0][it->second]);
      for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
      {
        if (i != it->second)
        {
          newVars.emplace_back(q[0][i]);
        }
      }
      std::vector<Node> qc(q.begin(), q.end());
      NodeManager* nm = nodeManager();
      qc[0] = nm->mkNode(Kind::BOUND_VAR_LIST, newVars);
      Node qn = nm->mkNode(Kind::FORALL, qc);
      Node eqq = q.eqNode(qn);
      cdp.addStep(eqq, ProofRule::QUANT_VAR_REORDERING, {}, {eqq});
      transEq.emplace_back(eqq);
      q = qn;
    }
    Node eqq2 = q.eqNode(fact[1]);
    cdp.addTheoryRewriteStep(eqq2, ProofRewriteRule::QUANT_DT_SPLIT);
    if (!transEq.empty())
    {
      transEq.emplace_back(eqq2);
      cdp.addStep(fact, ProofRule::TRANS, transEq, {});
    }
    return cdp.getProofFor(fact);
  }
  /** identify */
  std::string identify() const override { return "QuantDSplitProofGenerator"; }
  /**
   * Notify that the given lemma used the given variable index to split. We
   * store this in d_index and use it to guide proof reconstruction above.
   */
  void notifyLemma(const Node& lem, size_t index) { d_index[lem] = index; }

 private:
  /** Mapping from lemmas to their notified index */
  context::CDHashMap<Node, size_t> d_index;
};

/**
 * Attributes used for constructing bound variables in a canonical way. These
 * are attributes that map to bound variable, introduced for the following
 * purpose:
 * - QDSplitVarAttribute: cached on (q, v, i) where QuantDSplit::split is called
 * to split the variable v of q. We introduce bound variables, where the i^th
 * variable created in that method is cached based on i.
 */
struct QDSplitVarAttributeId
{
};
using QDSplitVarAttribute = expr::Attribute<QDSplitVarAttributeId, Node>;

QuantDSplit::QuantDSplit(Env& env,
                         QuantifiersState& qs,
                         QuantifiersInferenceManager& qim,
                         QuantifiersRegistry& qr,
                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_quant_to_reduce(userContext()),
      d_added_split(userContext()),
      d_pfgen(options().smt.produceProofs ? new QuantDSplitProofGenerator(d_env)
                                          : nullptr)
{
}

void QuantDSplit::checkOwnership(Node q)
{
  // If q is non-standard (marked as sygus, quantifier elimination, etc.), then
  // do no split it.
  QAttributes qa;
  QuantAttributes::computeQuantAttributes(q, qa);
  if (!qa.isStandard())
  {
    return;
  }
  // do not split if there is a trigger
  if (qa.d_hasPattern)
  {
    return;
  }
  bool takeOwnership = false;
  bool doSplit = false;
  QuantifiersBoundInference& qbi = d_qreg.getQuantifiersBoundInference();
  Trace("quant-dsplit-debug") << "Check split quantified formula : " << q << std::endl;
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    TypeNode tn = q[0][i].getType();
    if( tn.isDatatype() ){
      bool isFinite = d_env.isFiniteType(tn);
      const DType& dt = tn.getDType();
      if (dt.isRecursiveSingleton(tn))
      {
        Trace("quant-dsplit-debug") << "Datatype " << dt.getName() << " is recursive singleton." << std::endl;
      }
      else
      {
        if (options().quantifiers.quantDynamicSplit
            == options::QuantDSplitMode::AGG)
        {
          // split if it is a finite datatype
          doSplit = isFinite;
        }
        else if (options().quantifiers.quantDynamicSplit
                 == options::QuantDSplitMode::DEFAULT)
        {
          if (!qbi.isFiniteBound(q, q[0][i]))
          {
            if (isFinite)
            {
              // split if goes from being unhandled -> handled by finite
              // instantiation. An example is datatypes with uninterpreted sort
              // fields which are "interpreted finite" but not "finite".
              doSplit = true;
              // we additionally take ownership of this formula, in other words,
              // we mark it reduced.
              takeOwnership = true;
            }
            else if (dt.getNumConstructors() == 1 && !dt.isCodatatype())
            {
              // split if only one constructor
              doSplit = true;
            }
          }
        }
        if (doSplit)
        {
          // store the index to split
          d_quant_to_reduce[q] = i;
          Trace("quant-dsplit-debug")
              << "Split at index " << i << " based on datatype " << dt.getName()
              << std::endl;
          break;
        }
        Trace("quant-dsplit-debug")
            << "Do not split based on datatype " << dt.getName() << std::endl;
      }
    }
  }

  if (takeOwnership)
  {
    Trace("quant-dsplit-debug") << "Will take ownership." << std::endl;
    d_qreg.setOwner(q, this);
  }
  // Notice we may not take ownership in some cases, meaning that both the
  // original quantified formula and the split one are generated. This may
  // increase our ability to answer "unsat", since quantifier instantiation
  // heuristics may be more effective for one or the other (see issues #993
  // and 3481).
}

/* whether this module needs to check this round */
bool QuantDSplit::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_FULL && !d_quant_to_reduce.empty();
}

bool QuantDSplit::checkCompleteFor( Node q ) {
  // true if we split q
  return d_added_split.find( q )!=d_added_split.end();
}

/* Call during quantifier engine's check */
void QuantDSplit::check(Theory::Effort e, QEffort quant_e)
{
  //add lemmas ASAP (they are a reduction)
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  Trace("quant-dsplit") << "QuantDSplit::check" << std::endl;
  FirstOrderModel* m = d_treg.getModel();
  for (NodeIntMap::iterator it = d_quant_to_reduce.begin();
       it != d_quant_to_reduce.end();
       ++it)
  {
    Node q = it->first;
    Trace("quant-dsplit") << "- Split quantifier " << q << std::endl;
    if (d_added_split.find(q) != d_added_split.end())
    {
      continue;
    }
    if (m->isQuantifierAsserted(q) && m->isQuantifierActive(q))
    {
      d_added_split.insert(q);
      Node qsplit = split(nodeManager(), q, it->second);
      Node lem = q.eqNode(qsplit);
      // must remember the variable index if proofs are enabled
      if (d_pfgen != nullptr)
      {
        d_pfgen->notifyLemma(lem, it->second);
      }
      Trace("quant-dsplit") << "QuantDSplit lemma : " << lem << std::endl;
      d_qim.addPendingLemma(lem,
                            InferenceId::QUANTIFIERS_DSPLIT,
                            LemmaProperty::NONE,
                            d_pfgen.get());
    }
  }
  Trace("quant-dsplit") << "QuantDSplit::check finished" << std::endl;
}

Node QuantDSplit::split(NodeManager* nm, const Node& q, size_t index)
{
  std::vector<Node> bvs;
  for (size_t i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    if (i != index)
    {
      bvs.push_back(q[0][i]);
    }
  }
  TNode svar = q[0][index];
  TypeNode tn = svar.getType();
  Assert(tn.isDatatype());
  std::vector<Node> cons;
  const DType& dt = tn.getDType();
  BoundVarManager* bvm = nm->getBoundVarManager();
  size_t varCount = 0;
  for (size_t j = 0, ncons = dt.getNumConstructors(); j < ncons; j++)
  {
    std::vector<Node> vars;
    TypeNode dtjtn = dt[j].getInstantiatedConstructorType(tn);
    Assert(dtjtn.getNumChildren() == dt[j].getNumArgs() + 1);
    for (size_t k = 0, nargs = dt[j].getNumArgs(); k < nargs; k++)
    {
      TypeNode tns = dtjtn[k];
      Node cacheVal = bvm->getCacheValue(q[1], q[0][index], varCount);
      varCount++;
      Node v = bvm->mkBoundVar<QDSplitVarAttribute>(cacheVal, tns);
      vars.push_back(v);
    }
    std::vector<Node> bvs_cmb;
    bvs_cmb.insert(bvs_cmb.end(), bvs.begin(), bvs.end());
    bvs_cmb.insert(bvs_cmb.end(), vars.begin(), vars.end());
    Node c = datatypes::utils::mkApplyCons(tn, dt, j, vars);
    TNode ct = c;
    Node body = q[1].substitute(svar, ct);
    if (!bvs_cmb.empty())
    {
      Node bvl = nm->mkNode(Kind::BOUND_VAR_LIST, bvs_cmb);
      std::vector<Node> children;
      children.push_back(bvl);
      children.push_back(body);
      if (q.getNumChildren() == 3)
      {
        Node ipls = q[2].substitute(svar, ct);
        children.push_back(ipls);
      }
      body = nm->mkNode(Kind::FORALL, children);
    }
    cons.push_back(body);
  }
  return nm->mkAnd(cons);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

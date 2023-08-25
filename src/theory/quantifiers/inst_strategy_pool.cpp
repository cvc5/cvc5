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
 * Pool-based instantiation strategy
 */

#include "theory/quantifiers/inst_strategy_pool.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategyPool::InstStrategyPool(Env& env,
                                   QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   QuantifiersRegistry& qr,
                                   TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

void InstStrategyPool::presolve() {}

bool InstStrategyPool::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void InstStrategyPool::reset_round(Theory::Effort e) {}

void InstStrategyPool::registerQuantifier(Node q)
{
  if (options().quantifiers.userPoolQuant == options::UserPoolMode::IGNORE)
  {
    return;
  }
  // take into account user pools
  if (q.getNumChildren() == 3)
  {
    Node subsPat = d_qreg.substituteBoundVariablesToInstConstants(q[2], q);
    // add patterns
    for (const Node& p : subsPat)
    {
      if (p.getKind() == INST_POOL)
      {
        d_userPools[q].push_back(p);
      }
    }
  }
}

void InstStrategyPool::checkOwnership(Node q)
{
  if (options().quantifiers.userPoolQuant == options::UserPoolMode::TRUST
      && q.getNumChildren() == 3)
  {
    // if only using pools for instantiation, take ownership of this quantified
    // formula
    for (const Node& p : q[2])
    {
      if (p.getKind() == INST_POOL)
      {
        d_qreg.setOwner(q, this, 1);
        return;
      }
    }
  }
}

bool InstStrategyPool::hasProductSemantics(Node q, Node p)
{
  Assert(q.getKind() == EXISTS || q.getKind() == FORALL);
  Assert(p.getKind() == INST_POOL);
  size_t nchild = p.getNumChildren();
  if (nchild != q[0].getNumChildren())
  {
    return false;
  }
  for (size_t i = 0; i < nchild; i++)
  {
    Assert(p[i].getType().isSet());
    TypeNode tn = p[i].getType().getSetElementType();
    if (tn != q[0][i].getType())
    {
      // the i^th pool in the annotation does not match the i^th variable
      return false;
    }
  }
  return true;
}

bool InstStrategyPool::hasTupleSemantics(Node q, Node p)
{
  Assert(q.getKind() == EXISTS || q.getKind() == FORALL);
  Assert(p.getKind() == INST_POOL);
  if (p.getNumChildren() != 1)
  {
    return false;
  }
  Assert(p[0].getType().isSet());
  TypeNode ptn = p[0].getType().getSetElementType();
  if (!ptn.isTuple())
  {
    return false;
  }
  std::vector<TypeNode> targs = ptn.getTupleTypes();
  size_t nchild = targs.size();
  if (nchild != q[0].getNumChildren())
  {
    return false;
  }
  for (size_t i = 0; i < nchild; i++)
  {
    if (targs[i] != q[0][i].getType())
    {
      // the i^th component type of the pool in the annotation does not match
      // the i^th variable
      return false;
    }
  }
  return true;
}

void InstStrategyPool::check(Theory::Effort e, QEffort quant_e)
{
  if (d_userPools.empty())
  {
    return;
  }
  double clSet = 0;
  if (TraceIsOn("pool-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("pool-engine") << "---Pool instantiation, effort = " << e << "---"
                         << std::endl;
  }
  FirstOrderModel* fm = d_treg.getModel();
  bool inConflict = false;
  uint64_t addedLemmas = 0;
  size_t nquant = fm->getNumAssertedQuantifiers();
  std::map<Node, std::vector<Node> >::iterator uit;
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = fm->getAssertedQuantifier(i, true);
    uit = d_userPools.find(q);
    if (uit == d_userPools.end())
    {
      // no user pools for this
      continue;
    }
    if (!d_qreg.hasOwnership(q, this))
    {
      // quantified formula is not owned by this
      continue;
    }
    // process with each user pool
    for (const Node& p : uit->second)
    {
      inConflict = process(q, p, addedLemmas);
      if (inConflict)
      {
        break;
      }
    }
    if (inConflict)
    {
      break;
    }
  }
  if (TraceIsOn("pool-engine"))
  {
    Trace("pool-engine") << "Added lemmas = " << addedLemmas << std::endl;
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("pool-engine") << "Finished pool instantiation, time = "
                         << (clSet2 - clSet) << std::endl;
  }
}

std::string InstStrategyPool::identify() const
{
  return std::string("InstStrategyPool");
}

bool InstStrategyPool::process(Node q, Node p, uint64_t& addedLemmas)
{
  Assert(q.getKind() == FORALL && p.getKind() == INST_POOL);
  // maybe has tuple semantics?
  if (hasTupleSemantics(q, p))
  {
    return processTuple(q, p, addedLemmas);
  }
  // otherwise, process standard
  Instantiate* ie = d_qim.getInstantiate();
  TermTupleEnumeratorEnv ttec;
  ttec.d_fullEffort = true;
  ttec.d_increaseSum = options().quantifiers.enumInstSum;
  ttec.d_tr = &d_treg;
  std::shared_ptr<TermTupleEnumeratorInterface> enumerator(
      mkTermTupleEnumeratorPool(q, &ttec, p));
  std::vector<Node> terms;
  std::vector<bool> failMask;
  // we instantiate exhaustively
  enumerator->init();
  while (enumerator->hasNext())
  {
    if (d_qstate.isInConflict())
    {
      // could be conflicting for an internal reason
      return true;
    }
    enumerator->next(terms);
    // try instantiation
    failMask.clear();
    if (ie->addInstantiationExpFail(
            q, terms, failMask, InferenceId::QUANTIFIERS_INST_POOL))
    {
      Trace("pool-inst") << "Success with " << terms << std::endl;
      addedLemmas++;
    }
    else
    {
      Trace("pool-inst") << "Fail with " << terms << std::endl;
      // notify the enumerator of the failure
      enumerator->failureReason(failMask);
    }
  }
  return false;
}

bool InstStrategyPool::processTuple(Node q, Node p, uint64_t& addedLemmas)
{
  Instantiate* ie = d_qim.getInstantiate();
  TermPools* tp = d_treg.getTermPools();
  // get the terms
  std::vector<Node> terms;
  tp->getTermsForPool(p[0], terms);
  // instantiation for each term in pool
  for (const Node& t : terms)
  {
    if (d_qstate.isInConflict())
    {
      return true;
    }
    if (t.getKind() != APPLY_CONSTRUCTOR)
    {
      // a symbolic tuple is in the pool, we ignore it.
      continue;
    }
    std::vector<Node> inst(t.begin(), t.end());
    Assert(inst.size() == q[0].getNumChildren());
    if (ie->addInstantiation(q, inst, InferenceId::QUANTIFIERS_INST_POOL_TUPLE))
    {
      Trace("pool-inst") << "Success (tuple) with " << inst << std::endl;
      addedLemmas++;
    }
    else
    {
      Trace("pool-inst") << "Fail (tuple) with " << inst << std::endl;
    }
  }
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

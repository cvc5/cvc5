/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

using namespace cvc5::kind;
using namespace cvc5::context;

namespace cvc5 {
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

void InstStrategyPool::check(Theory::Effort e, QEffort quant_e)
{
  if (d_userPools.empty())
  {
    return;
  }
  double clSet = 0;
  if (Trace.isOn("pool-engine"))
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
    if (!d_qreg.hasOwnership(q, this) || !fm->isQuantifierActive(q))
    {
      // quantified formula is not owned by this or is inactive
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
  if (Trace.isOn("pool-engine"))
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
  TermTupleEnumeratorEnv ttec;
  ttec.d_fullEffort = true;
  ttec.d_increaseSum = options().quantifiers.fullSaturateSum;
  TermPools* tp = d_treg.getTermPools();
  std::shared_ptr<TermTupleEnumeratorInterface> enumerator(
      mkTermTupleEnumeratorPool(q, &ttec, tp, p));
  Instantiate* ie = d_qim.getInstantiate();
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * All eager quantifier instantiation
 */

#include "theory/quantifiers/inst_strategy_sub_conflict.h"

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "theory/quantifiers/instantiation_list.h"
#include "theory/smt_engine_subsolver.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstStrategySubConflict::InstStrategySubConflict(
    Env& env,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // requires full proofs
  d_subOptions.writeSmt().produceProofs = true;
  // don't do simplification, which can preprocess quantifiers to those not
  // occurring in the main solver
  d_subOptions.writeSmt().simplificationMode =
      options::SimplificationMode::NONE;
  // don't do this strategy
  d_subOptions.writeQuantifiers().quantSubCbqi = false;
}

void InstStrategySubConflict::reset_round(Theory::Effort e) {}

bool InstStrategySubConflict::needsCheck(Theory::Effort e)
{
  return !d_qstate.isInConflict();
}

void InstStrategySubConflict::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  double clSet = 0;
  if (TraceIsOn("qscf-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qscf-engine") << "---Subconflict Find Engine Round---" << std::endl;
  }
  std::vector<Node> assertions;
  std::unordered_set<Node> quants;
  const LogicInfo& logicInfo = d_qstate.getLogicInfo();
  for (TheoryId tid = THEORY_FIRST; tid < THEORY_LAST; ++tid)
  {
    if (!logicInfo.isTheoryEnabled(tid))
    {
      continue;
    }
    // collect all assertions from theory
    for (context::CDList<Assertion>::const_iterator
             it = d_qstate.factsBegin(tid),
             itEnd = d_qstate.factsEnd(tid);
         it != itEnd;
         ++it)
    {
      Node a = (*it).d_assertion;
      assertions.push_back(a);
      if (tid == THEORY_QUANTIFIERS)
      {
        if (a.getKind() == Kind::FORALL)
        {
          quants.insert(a);
        }
      }
    }
  }
  // do subsolver check
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  std::unique_ptr<SolverEngine> findConflict;
  uint64_t timeout = options().quantifiers.quantSubCbqiTimeout;
  initializeSubsolver(findConflict, ssi, timeout != 0, timeout);
  // assert and check-sat
  for (const Node& a : assertions)
  {
    findConflict->assertFormula(a);
  }
  Trace("qscf-engine") << ">>> Check subsolver..." << std::endl;
  Result r = findConflict->checkSat();
  Trace("qscf-engine") << "<<< ...result is " << r << std::endl;
  size_t addedLemmas = 0;
  if (r.getStatus() == Result::UNSAT)
  {
    bool completeConflict = true;
    // now get relevant instantiations
    std::map<Node, InstantiationList> insts;
    std::map<Node, std::vector<Node>> sks;
    findConflict->getRelevantQuantTermVectors(insts, sks);
    Instantiate* qinst = d_qim.getInstantiate();
    for (std::pair<const Node, InstantiationList>& i : insts)
    {
      // ensure we have this quantified formula asserted
      Node q = i.first;
      if (quants.find(q) == quants.end())
      {
        // the conflict is not complete
        completeConflict = false;
        continue;
      }
      // otherwise instantiate
      for (InstantiationVec& vec : i.second)
      {
        if (qinst->addInstantiation(
                q, vec.d_vec, InferenceId::QUANTIFIERS_INST_SUB_CONFLICT))
        {
          addedLemmas++;
        }
      }
    }
    if (completeConflict)
    {
      d_qstate.notifyConflictingInst();
    }
  }

  if (TraceIsOn("qscf-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("qscf-engine") << "Finished subconflict find engine, time = "
                         << (clSet2 - clSet);
    if (addedLemmas > 0)
    {
      Trace("qscf-engine") << ", addedLemmas = " << addedLemmas;
    }
    Trace("qscf-engine") << std::endl;
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

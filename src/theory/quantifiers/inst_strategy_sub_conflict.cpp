/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Subsolver conflict quantifier instantiation
 */

#include "theory/quantifiers/inst_strategy_sub_conflict.h"

#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "proof/unsat_core.h"
#include "smt/set_defaults.h"
#include "theory/quantifiers/instantiate.h"
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
  // disable checking first
  smt::SetDefaults::disableChecking(d_subOptions);
  // requires full proofs
  d_subOptions.write_smt().produceProofs = true;
  // don't do simplification, which can preprocess quantifiers to those not
  // occurring in the main solver
  d_subOptions.write_smt().simplificationMode =
      options::SimplificationMode::NONE;
  // requires unsat cores
  d_subOptions.write_smt().produceUnsatCores = true;
  // don't do this strategy
  d_subOptions.write_quantifiers().quantSubCbqi = false;
  // initialize the trust proof generator if necessary
  if (d_env.isTheoryProofProducing())
  {
    d_tpg.reset(
        new TrustProofGenerator(env, TrustId::QUANTIFIERS_SUB_CBQI_LEMMA, {}));
  }
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
  if (e != Theory::EFFORT_LAST_CALL)
  {
    return;
  }
  beginCallDebug();
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
      if (tid == THEORY_QUANTIFIERS)
      {
        if (a.getKind() == Kind::FORALL)
        {
          quants.insert(a);
        }
      }
      assertions.push_back(a);
    }
  }
  // if no quantified formulas, no use
  if (quants.empty())
  {
    return;
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
    // now get relevant instantiations
    std::map<Node, InstantiationList> insts;
    std::map<Node, std::vector<Node>> sks;
    findConflict->getRelevantQuantTermVectors(insts, sks);
    Instantiate* qinst = d_qim.getInstantiate();
    size_t triedLemmas = 0;
    for (std::pair<const Node, InstantiationList>& i : insts)
    {
      // ensure we have this quantified formula asserted
      Node q = i.first;
      if (quants.find(q) == quants.end())
      {
        // We ignore this instantiation. We could throw a debug assertion
        // failure to catch these, however, there is no strong guarantee
        // that our preprocessor will preserve the shapes of all quantified
        // formulas, hence we just continue.
        continue;
      }
      // otherwise instantiate
      std::vector<InstantiationVec>& ilist = i.second.d_inst;
      for (InstantiationVec& vec : ilist)
      {
        if (qinst->addInstantiation(
                q, vec.d_vec, InferenceId::QUANTIFIERS_INST_SUB_CONFLICT))
        {
          addedLemmas++;
        }
        triedLemmas++;
      }
    }
    // Note that it may be the case that addedLemmas = 0 and we found a
    // conflict. This indicates that the current assertions are unsat,
    // and can be shown independent of quantified formulas. We will backtrack
    // regardless since we assert the unsat core below.
    Trace("qscf-engine-debug")
        << addedLemmas << "/" << triedLemmas << " instantiated" << std::endl;
    // Add the computed unsat core as a conflict, which will cause a backtrack.
    UnsatCore uc = findConflict->getUnsatCore();
    Node ucc = nodeManager()->mkAnd(uc.getCore());
    Trace("qscf-engine-debug") << "Unsat core is " << ucc << std::endl;
    Trace("qscf-engine") << "Core size = " << uc.getCore().size() << std::endl;
    TrustNode trn = TrustNode::mkTrustLemma(ucc.notNode(), d_tpg.get());
    d_qim.trustedLemma(trn, InferenceId::QUANTIFIERS_SUB_UC);
    // also mark conflicting instance
    d_qstate.notifyConflictingInst();
  }

  endCallDebug();
}

std::string InstStrategySubConflict::identify() const { return "sub-cbqi"; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

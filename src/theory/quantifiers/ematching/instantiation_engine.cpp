/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of instantiation engine class
 */

#include "theory/quantifiers/ematching/instantiation_engine.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching_user.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;
using namespace cvc5::internal::theory::quantifiers::inst;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

InstantiationEngine::InstantiationEngine(Env& env,
                                         QuantifiersState& qs,
                                         QuantifiersInferenceManager& qim,
                                         QuantifiersRegistry& qr,
                                         TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_instStrategies(),
      d_isup(),
      d_i_ag(),
      d_quants(),
      d_trdb(d_env, qs, qim, qr, tr),
      d_quant_rel(nullptr)
{
  if (options().quantifiers.relevantTriggers)
  {
    d_quant_rel.reset(new quantifiers::QuantRelevance(env));
  }
  if (options().quantifiers.eMatching)
  {
    // these are the instantiation strategies for E-matching
    // user-provided patterns
    if (options().quantifiers.userPatternsQuant != options::UserPatMode::IGNORE)
    {
      d_isup.reset(
          new InstStrategyUserPatterns(d_env, d_trdb, qs, qim, qr, tr));
      d_instStrategies.push_back(d_isup.get());
    }

    // auto-generated patterns
    d_i_ag.reset(new InstStrategyAutoGenTriggers(
        d_env, d_trdb, qs, qim, qr, tr, d_quant_rel.get()));
    d_instStrategies.push_back(d_i_ag.get());
  }
}

InstantiationEngine::~InstantiationEngine() {}

std::string InstantiationEngine::identify() const { return "InstEngine"; }

void InstantiationEngine::presolve() {
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    d_instStrategies[i]->presolve();
  }
}

void InstantiationEngine::doInstantiationRound( Theory::Effort effort ){
  size_t lastWaiting = d_qim.numPendingLemmas();
  //iterate over an internal effort level e
  int e = 0;
  int eLimit = effort==Theory::EFFORT_LAST_CALL ? 10 : 2;
  bool finished = false;
  //while unfinished, try effort level=0,1,2....
  while( !finished && e<=eLimit ){
    Trace("inst-engine-debug") << "IE: Prepare instantiation (" << e << ")." << std::endl;
    finished = true;
    //instantiate each quantifier
    for( unsigned i=0; i<d_quants.size(); i++ ){
      Node q = d_quants[i];
      Trace("inst-engine-debug") << "IE: Instantiate " << q << "..." << std::endl;
      //int e_use = d_quantEngine->getRelevance( q )==-1 ? e - 1 : e;
      int e_use = e;
      if( e_use>=0 ){
        Trace("inst-engine-debug") << "inst-engine : " << q << std::endl;
        //check each instantiation strategy
        for( unsigned j=0; j<d_instStrategies.size(); j++ ){
          InstStrategy* is = d_instStrategies[j];
          Trace("inst-engine-debug") << "Do " << is->identify() << " " << e_use << std::endl;
          InstStrategyStatus quantStatus = is->process(q, effort, e_use);
          Trace("inst-engine-debug")
              << " -> unfinished= "
              << (quantStatus == InstStrategyStatus::STATUS_UNFINISHED)
              << ", conflict=" << d_qstate.isInConflict() << std::endl;
          if (d_qstate.isInConflict())
          {
            return;
          }
          else if (quantStatus == InstStrategyStatus::STATUS_UNFINISHED)
          {
            finished = false;
          }
        }
      }
    }
    //do not consider another level if already added lemma at this level
    if (d_qim.numPendingLemmas() > lastWaiting)
    {
      finished = true;
    }
    e++;
  }
}

bool InstantiationEngine::needsCheck( Theory::Effort e ){
  return d_qstate.getInstWhenNeedsCheck(e);
}

void InstantiationEngine::reset_round( Theory::Effort e ){
  //if not, proceed to instantiation round
  //reset the instantiation strategies
  for( unsigned i=0; i<d_instStrategies.size(); ++i ){
    InstStrategy* is = d_instStrategies[i];
    is->processResetInstantiationRound( e );
  }
}

void InstantiationEngine::check(Theory::Effort e, QEffort quant_e)
{
  CodeTimer codeTimer(d_qstate.getStats().d_ematching_time);
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  double clSet = 0;
  if (TraceIsOn("inst-engine"))
  {
    clSet = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("inst-engine") << "---Instantiation Engine Round, effort = " << e
                         << "---" << std::endl;
  }
  // collect all active quantified formulas belonging to this
  bool quantActive = false;
  d_quants.clear();
  FirstOrderModel* m = d_treg.getModel();
  size_t nquant = m->getNumAssertedQuantifiers();
  for (size_t i = 0; i < nquant; i++)
  {
    Node q = m->getAssertedQuantifier(i, true);
    if (shouldProcess(q) && m->isQuantifierActive(q))
    {
      quantActive = true;
      d_quants.push_back(q);
    }
  }
  Trace("inst-engine-debug")
      << "InstEngine: check: # asserted quantifiers " << d_quants.size() << "/";
  Trace("inst-engine-debug") << nquant << " " << quantActive << std::endl;
  if (quantActive)
  {
    size_t lastWaiting = d_qim.numPendingLemmas();
    doInstantiationRound(e);
    if (d_qstate.isInConflict())
    {
      Assert(d_qim.numPendingLemmas() > lastWaiting);
      Trace("inst-engine") << "Conflict, added lemmas = "
                           << (d_qim.numPendingLemmas() - lastWaiting)
                           << std::endl;
    }
    else if (d_qim.hasPendingLemma())
    {
      Trace("inst-engine") << "Added lemmas = "
                           << (d_qim.numPendingLemmas() - lastWaiting)
                           << std::endl;
    }
  }
  else
  {
    d_quants.clear();
  }
  if (TraceIsOn("inst-engine"))
  {
    double clSet2 = double(clock()) / double(CLOCKS_PER_SEC);
    Trace("inst-engine") << "Finished instantiation engine, time = "
                         << (clSet2 - clSet) << std::endl;
  }
}

bool InstantiationEngine::checkCompleteFor( Node q ) {
  //TODO?
  return false;
}

void InstantiationEngine::checkOwnership(Node q)
{
  if (options().quantifiers.userPatternsQuant == options::UserPatMode::STRICT
      && q.getNumChildren() == 3)
  {
    //if strict triggers, take ownership of this quantified formula
    if (QuantAttributes::hasPattern(q))
    {
      d_qreg.setOwner(q, this, 1);
    }
  }
}

void InstantiationEngine::registerQuantifier(Node q)
{
  if (!shouldProcess(q))
  {
    return;
  }
  if (d_quant_rel)
  {
    d_quant_rel->registerQuantifier(q);
  }
  // take into account user patterns
  if (q.getNumChildren() == 3)
  {
    Node subsPat = d_qreg.substituteBoundVariablesToInstConstants(q[2], q);
    // add patterns
    for (const Node& p : subsPat)
    {
      if (p.getKind() == INST_PATTERN)
      {
        addUserPattern(q, p);
      }
      else if (p.getKind() == INST_NO_PATTERN)
      {
        addUserNoPattern(q, p);
      }
    }
  }
}

void InstantiationEngine::addUserPattern(Node q, Node pat) {
  if (d_isup) {
    d_isup->addUserPattern(q, pat);
  }
}

void InstantiationEngine::addUserNoPattern(Node q, Node pat) {
  if (d_i_ag) {
    d_i_ag->addUserNoPattern(q, pat);
  }
}

bool InstantiationEngine::shouldProcess(Node q)
{
  if (!d_qreg.hasOwnership(q, this))
  {
    return false;
  }
  // also ignore internal quantifiers
  QuantAttributes& qattr = d_qreg.getQuantAttributes();
  if (qattr.isQuantBounded(q))
  {
    return false;
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

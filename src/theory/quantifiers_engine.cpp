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
 * Implementation of quantifiers engine class.
 */

#include "theory/quantifiers_engine.h"

#include "options/base_options.h"
#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/strings_options.h"
#include "options/uf_options.h"
#include "theory/quantifiers/equality_query.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/first_order_model_fmc.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/quantifiers/fmf/model_builder.h"
#include "theory/quantifiers/ieval/inst_evaluator_manager.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_modules.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/quantifiers_statistics.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/theory_engine.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

QuantifiersEngine::QuantifiersEngine(
    Env& env,
    quantifiers::QuantifiersState& qs,
    quantifiers::QuantifiersRegistry& qr,
    quantifiers::TermRegistry& tr,
    quantifiers::QuantifiersInferenceManager& qim,
    ProofNodeManager* pnm)
    : EnvObj(env),
      d_qstate(qs),
      d_qim(qim),
      d_te(nullptr),
      d_pnm(pnm),
      d_qreg(qr),
      d_treg(tr),
      d_model(nullptr),
      d_quants_prereg(userContext()),
      d_quants_red(userContext()),
      d_numInstRoundsLemma(0)
{
  options::FmfMbqiMode mmode = options().quantifiers.fmfMbqiMode;
  Trace("quant-init-debug")
      << "Initialize model engine, mbqi : " << mmode << " "
      << options().quantifiers.fmfBound << std::endl;
  // Finite model finding requires specialized ways of building the model.
  // We require constructing the model here, since it is required for
  // initializing the CombinationEngine and the rest of quantifiers engine.
  if (options().quantifiers.fmfBound || options().strings.stringExp
      || (options().quantifiers.finiteModelFind
          && (mmode == options::FmfMbqiMode::FMC
              || mmode == options::FmfMbqiMode::TRUST)))
  {
    Trace("quant-init-debug") << "...make fmc builder." << std::endl;
    d_builder.reset(
        new quantifiers::fmcheck::FullModelChecker(env, qs, qim, qr, tr));
  }
  else
  {
    Trace("quant-init-debug") << "...make default model builder." << std::endl;
    d_builder.reset(new quantifiers::QModelBuilder(env, qs, qim, qr, tr));
  }
  // set the model object
  d_builder->finishInit();
  d_model = d_builder->getModel();

  // Finish initializing the term registry by hooking it up to the model and the
  // inference manager. The former is required since theories are not given
  // access to the model in their constructors currently.
  // The latter is required due to a cyclic dependency between the term
  // database and the instantiate module. Term database needs inference manager
  // since it sends out lemmas when term indexing is inconsistent, instantiate
  // needs term database for entailment checks.
  d_treg.finishInit(d_model, &d_qim);

  // initialize the utilities
  d_util.push_back(d_model->getEqualityQuery());
  // quantifiers registry must come before the remaining utilities
  d_util.push_back(&d_qreg);
  d_util.push_back(tr.getTermDatabase());
  d_util.push_back(qim.getInstantiate());
  d_util.push_back(tr.getTermPools());
  d_util.push_back(tr.getInstEvaluatorManager());
}

QuantifiersEngine::~QuantifiersEngine() {}

void QuantifiersEngine::finishInit(TheoryEngine* te)
{
  // connect the quantifiers model to the underlying theory model
  d_model->finishInit(te->getModel());
  d_te = te;
  // Initialize the modules and the utilities here.
  d_qmodules.reset(new quantifiers::QuantifiersModules());
  d_qmodules->initialize(
      d_env, d_qstate, d_qim, d_qreg, d_treg, d_builder.get(), d_modules);
  if (d_qmodules->d_rel_dom.get())
  {
    d_util.push_back(d_qmodules->d_rel_dom.get());
  }

  // handle any circular dependencies

  // quantifiers bound inference needs to be informed of the bounded integers
  // module, which has information about which quantifiers have finite bounds
  d_qreg.getQuantifiersBoundInference().finishInit(d_qmodules->d_bint.get());
}

quantifiers::QuantifiersRegistry& QuantifiersEngine::getQuantifiersRegistry()
{
  return d_qreg;
}

quantifiers::QModelBuilder* QuantifiersEngine::getModelBuilder() const
{
  return d_builder.get();
}

/// !!!!!!!!!!!!!! temporary (project #15)

quantifiers::TermDbSygus* QuantifiersEngine::getTermDatabaseSygus() const
{
  return d_treg.getTermDatabaseSygus();
}
/// !!!!!!!!!!!!!!

void QuantifiersEngine::presolve() {
  Trace("quant-engine-proc") << "QuantifiersEngine : presolve " << std::endl;
  d_numInstRoundsLemma = 0;
  d_qim.clearPending();
  for (QuantifiersUtil*& u : d_util)
  {
    u->presolve();
  }
  for (QuantifiersModule*& mdl : d_modules)
  {
    mdl->presolve();
  }
  // presolve with term registry, which populates the term database based on
  // terms registered before presolve when in incremental mode
  d_treg.presolve();
}

void QuantifiersEngine::ppNotifyAssertions(
    const std::vector<Node>& assertions) {
  Trace("quant-engine-proc")
      << "ppNotifyAssertions in QE, #assertions = " << assertions.size()
      << std::endl;
  if (options().quantifiers.instMaxLevel != -1)
  {
    for (const Node& a : assertions)
    {
      quantifiers::QuantAttributes::setInstantiationLevelAttr(a, 0);
    }
  }
  if (options().quantifiers.sygus)
  {
    quantifiers::SynthEngine* sye = d_qmodules->d_synth_e.get();
    for (const Node& a : assertions)
    {
      sye->ppNotifyAssertion(a);
    }
  }
  /* The SyGuS instantiation module needs a global view of all available
   * assertions to collect global terms that get added to each grammar.
   */
  if (options().quantifiers.sygusInst)
  {
    quantifiers::SygusInst* si = d_qmodules->d_sygus_inst.get();
    si->ppNotifyAssertions(assertions);
  }
}

void QuantifiersEngine::check( Theory::Effort e ){
  quantifiers::QuantifiersStatistics& stats = d_qstate.getStats();
  CodeTimer codeTimer(stats.d_time);
  Assert(d_qstate.getEqualityEngine() != nullptr);
  if (!d_qstate.getEqualityEngine()->consistent())
  {
    Trace("quant-engine-debug") << "Master equality engine not consistent, return." << std::endl;
    return;
  }
  if (d_qstate.isInConflict())
  {
    if (e < Theory::EFFORT_LAST_CALL)
    {
      // this can happen in rare cases when quantifiers is the first to realize
      // there is a quantifier-free conflict, for example, when it discovers
      // disequal and congruent terms in the master equality engine during
      // term indexing. In such cases, quantifiers reports a "conflicting lemma"
      // that is, one that is entailed to be false by the current assignment.
      // If this lemma is not a SAT conflict, we may get another call to full
      // effort check and the quantifier-free solvers still haven't realized
      // there is a conflict. In this case, we return, trusting that theory
      // combination will do the right thing (split on equalities until there is
      // a conflict at the quantifier-free level).
      Trace("quant-engine-debug")
          << "Conflicting lemma already reported by quantifiers, return."
          << std::endl;
      return;
    }
    // we reported what we thought was a conflicting lemma, but now we have
    // gotten a check at LAST_CALL effort, indicating that the lemma we reported
    // was not conflicting. This should never happen, but in production mode, we
    // proceed with the check.
    Assert(false);
  }
  bool needsCheck = d_qim.hasPendingLemma();
  QuantifiersModule::QEffort needsModelE = QuantifiersModule::QEFFORT_NONE;
  std::vector< QuantifiersModule* > qm;
  if( d_model->checkNeeded() ){
    needsCheck = needsCheck || e>=Theory::EFFORT_LAST_CALL;  //always need to check at or above last call
    for (QuantifiersModule*& mdl : d_modules)
    {
      if (mdl->needsCheck(e))
      {
        qm.push_back(mdl);
        needsCheck = true;
        //can only request model at last call since theory combination can find inconsistencies
        if( e>=Theory::EFFORT_LAST_CALL ){
          QuantifiersModule::QEffort me = mdl->needsModel(e);
          needsModelE = me<needsModelE ? me : needsModelE;
        }
      }
    }
  }

  d_qim.reset();
  bool setModelUnsound = false;
  IncompleteId setModelUnsoundId = IncompleteId::QUANTIFIERS;
  if (options().quantifiers.instMaxRounds >= 0
      && d_numInstRoundsLemma
             >= static_cast<uint32_t>(options().quantifiers.instMaxRounds))
  {
    needsCheck = false;
    setModelUnsound = true;
    setModelUnsoundId = IncompleteId::QUANTIFIERS_MAX_INST_ROUNDS;
  }

  Trace("quant-engine-debug2") << "Quantifiers Engine call to check, level = " << e << ", needsCheck=" << needsCheck << std::endl;
  if( needsCheck ){
    //flush previous lemmas (for instance, if was interrupted), or other lemmas to process
    d_qim.doPending();
    if (d_qim.hasSentLemma())
    {
      return;
    }

    double clSet = 0;
    if( TraceIsOn("quant-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("quant-engine") << ">>>>> Quantifiers Engine Round, effort = " << e << " <<<<<" << std::endl;
    }

    if( TraceIsOn("quant-engine-debug") ){
      Trace("quant-engine-debug") << "Quantifiers Engine check, level = " << e << std::endl;
      Trace("quant-engine-debug")
          << "  depth : " << d_qstate.getInstRoundDepth() << std::endl;
      Trace("quant-engine-debug") << "  modules to check : ";
      for( unsigned i=0; i<qm.size(); i++ ){
        Trace("quant-engine-debug") << qm[i]->identify() << " ";
      }
      Trace("quant-engine-debug") << std::endl;
      Trace("quant-engine-debug") << "  # quantified formulas = " << d_model->getNumAssertedQuantifiers() << std::endl;
      if (d_qim.hasPendingLemma())
      {
        Trace("quant-engine-debug")
            << "  lemmas waiting = " << d_qim.numPendingLemmas() << std::endl;
      }
      Trace("quant-engine-debug")
          << "  Theory engine finished : "
          << !d_qstate.getValuation().needCheck() << std::endl;
      Trace("quant-engine-debug") << "  Needs model effort : " << needsModelE << std::endl;
      Trace("quant-engine-debug")
          << "  In conflict : " << d_qstate.isInConflict() << std::endl;
    }
    if( TraceIsOn("quant-engine-ee-pre") ){
      Trace("quant-engine-ee-pre") << "Equality engine (pre-inference): " << std::endl;
      d_qstate.debugPrintEqualityEngine("quant-engine-ee-pre");
    }
    if( TraceIsOn("quant-engine-assert") ){
      Trace("quant-engine-assert") << "Assertions : " << std::endl;
      d_te->printAssertions("quant-engine-assert");
    }

    //reset utilities
    Trace("quant-engine-debug") << "Resetting all utilities..." << std::endl;
    for (QuantifiersUtil*& util : d_util)
    {
      Trace("quant-engine-debug2") << "Reset " << util->identify().c_str()
                                   << "..." << std::endl;
      if (!util->reset(e))
      {
        d_qim.doPending();
        if (d_qim.hasSentLemma())
        {
          return;
        }else{
          //should only fail reset if added a lemma
          Assert(false);
        }
      }
    }

    if( TraceIsOn("quant-engine-ee") ){
      Trace("quant-engine-ee") << "Equality engine : " << std::endl;
      d_qstate.debugPrintEqualityEngine("quant-engine-ee");
    }

    //reset the model
    Trace("quant-engine-debug") << "Reset model..." << std::endl;
    d_model->reset_round();

    //reset the modules
    Trace("quant-engine-debug") << "Resetting all modules..." << std::endl;
    for (QuantifiersModule*& mdl : d_modules)
    {
      Trace("quant-engine-debug2") << "Reset " << mdl->identify().c_str()
                                   << std::endl;
      mdl->reset_round(e);
    }
    Trace("quant-engine-debug") << "Done resetting all modules." << std::endl;
    //reset may have added lemmas
    d_qim.doPending();
    if (d_qim.hasSentLemma())
    {
      return;
    }

    if( e==Theory::EFFORT_LAST_CALL ){
      ++(stats.d_instantiation_rounds_lc);
    }else if( e==Theory::EFFORT_FULL ){
      ++(stats.d_instantiation_rounds);
    }
    Trace("quant-engine-debug") << "Check modules that needed check..." << std::endl;
    for (unsigned qef = QuantifiersModule::QEFFORT_CONFLICT;
         qef <= QuantifiersModule::QEFFORT_LAST_CALL;
         ++qef)
    {
      QuantifiersModule::QEffort quant_e =
          static_cast<QuantifiersModule::QEffort>(qef);
      // Force the theory engine to build the model if any module requested it.
      if (needsModelE == quant_e)
      {
        Trace("quant-engine-debug") << "Build model..." << std::endl;
        if (!d_te->buildModel())
        {
          // If we failed to build the model, flush all pending lemmas and
          // finish.
          d_qim.doPending();
          break;
        }
      }
      if (!d_qim.hasSentLemma())
      {
        //check each module
        for (QuantifiersModule*& mdl : qm)
        {
          Trace("quant-engine-debug") << "Check " << mdl->identify().c_str()
                                      << " at effort " << quant_e << "..."
                                      << std::endl;
          mdl->check(e, quant_e);
          if (d_qstate.isInConflict())
          {
            Trace("quant-engine-debug") << "...conflict!" << std::endl;
            break;
          }
        }
        //flush all current lemmas
        d_qim.doPending();
      }
      // If we have added a lemma, stop. We also stop if we are in conflict.
      // In very rare cases, it may be the case that quantifiers knows there
      // is a conflict without adding a lemma, e.g. if it sent a duplicate
      // QUANTIFIERS_TDB_DEQ_CONG lemma, which can occur if it has detected
      // a quantifier-free conflict during term indexing but the quantifier
      // free theories haven't caused a backtrack yet. This should never happen
      // at LAST_CALL effort.
      if (d_qim.hasSentLemma() || d_qstate.isInConflict())
      {
        Assert(d_qim.hasSentLemma() || e != Theory::EFFORT_LAST_CALL);
        break;
      }else{
        if (quant_e == QuantifiersModule::QEFFORT_CONFLICT)
        {
          d_qstate.incrementInstRoundCounters(e);
        }
        else if (quant_e == QuantifiersModule::QEFFORT_MODEL)
        {
          if( e==Theory::EFFORT_LAST_CALL ){
            //sources of incompleteness
            for (QuantifiersUtil*& util : d_util)
            {
              if (!util->checkComplete(setModelUnsoundId))
              {
                Trace("quant-engine-debug") << "Set incomplete because utility "
                                            << util->identify().c_str()
                                            << " was incomplete." << std::endl;
                setModelUnsound = true;
              }
            }
            if (d_qstate.isInConflict())
            {
              // we reported a conflicting lemma, should return
              setModelUnsound = true;
            }
            //if we have a chance not to set incomplete
            if (!setModelUnsound)
            {
              //check if we should set the incomplete flag
              for (QuantifiersModule*& mdl : d_modules)
              {
                if (!mdl->checkComplete(setModelUnsoundId))
                {
                  Trace("quant-engine-debug")
                      << "Set incomplete because module "
                      << mdl->identify().c_str() << " was incomplete."
                      << std::endl;
                  setModelUnsound = true;
                  break;
                }
              }
              if (!setModelUnsound)
              {
                //look at individual quantified formulas, one module must claim completeness for each one
                for( unsigned i=0; i<d_model->getNumAssertedQuantifiers(); i++ ){
                  bool hasCompleteM = false;
                  Node q = d_model->getAssertedQuantifier( i );
                  QuantifiersModule* qmd = d_qreg.getOwner(q);
                  if( qmd!=NULL ){
                    hasCompleteM = qmd->checkCompleteFor( q );
                  }else{
                    for( unsigned j=0; j<d_modules.size(); j++ ){
                      if( d_modules[j]->checkCompleteFor( q ) ){
                        qmd = d_modules[j];
                        hasCompleteM = true;
                        break;
                      }
                    }
                  }
                  if( !hasCompleteM ){
                    Trace("quant-engine-debug") << "Set incomplete because " << q << " was not fully processed." << std::endl;
                    setModelUnsound = true;
                    break;
                  }else{
                    Assert(qmd != NULL);
                    Trace("quant-engine-debug2") << "Complete for " << q << " due to " << qmd->identify().c_str() << std::endl;
                  }
                }
              }
            }
            // if setModelUnsound = false, we will answer SAT, otherwise we will
            // run at quant_e QEFFORT_LAST_CALL
            if (!setModelUnsound)
            {
              break;
            }
          }
        }
      }
    }
    Trace("quant-engine-debug") << "Done check modules that needed check." << std::endl;
    // debug print
    if (d_qim.hasSentLemma())
    {
      d_qim.getInstantiate()->notifyEndRound();
      d_numInstRoundsLemma++;
    }
    if( TraceIsOn("quant-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("quant-engine") << "Finished quantifiers engine, total time = " << (clSet2-clSet);
      Trace("quant-engine") << ", sent lemma = " << d_qim.hasSentLemma();
      Trace("quant-engine") << std::endl;
    }

    Trace("quant-engine-debug2") << "Finished quantifiers engine check." << std::endl;
  }else{
    Trace("quant-engine-debug2") << "Quantifiers Engine does not need check." << std::endl;
  }

  //SAT case
  if (e == Theory::EFFORT_LAST_CALL && !d_qim.hasSentLemma())
  {
    if (setModelUnsound)
    {
      Trace("quant-engine") << "Set incomplete flag." << std::endl;
      d_qim.setModelUnsound(setModelUnsoundId);
    }
    //output debug stats
    d_qim.getInstantiate()->debugPrintModel();
  }
  d_qim.clearPending();
}

void QuantifiersEngine::notifyCombineTheories() {
  // If allowing theory combination to happen at most once between instantiation
  // rounds, this would reset d_ierCounter to 1 and d_ierCounterLastLc to -1
  // in quantifiers state.
}

bool QuantifiersEngine::reduceQuantifier(Node q)
{
  // TODO: this can be unified with preregistration: AlphaEquivalence takes
  // ownership of reducable quants
  BoolMap::const_iterator it = d_quants_red.find(q);
  if (it == d_quants_red.end())
  {
    TrustNode tlem;
    InferenceId id = InferenceId::UNKNOWN;
    if (d_qmodules->d_alpha_equiv)
    {
      Trace("quant-engine-red")
          << "Alpha equivalence " << q << "?" << std::endl;
      // add equivalence with another quantified formula
      tlem = d_qmodules->d_alpha_equiv->reduceQuantifier(q);
      id = InferenceId::QUANTIFIERS_REDUCE_ALPHA_EQ;
      if (!tlem.isNull())
      {
        Trace("quant-engine-red")
            << "...alpha equivalence success." << std::endl;
        ++(d_qstate.getStats().d_red_alpha_equiv);
      }
    }
    if (!tlem.isNull())
    {
      d_qim.trustedLemma(tlem, id);
    }
    d_quants_red[q] = !tlem.isNull();
    return !tlem.isNull();
  }
  return (*it).second;
}

void QuantifiersEngine::registerQuantifierInternal(Node f)
{
  std::map< Node, bool >::iterator it = d_quants.find( f );
  if( it==d_quants.end() ){
    Trace("quant") << "QuantifiersEngine : Register quantifier ";
    Trace("quant") << " : " << f << std::endl;
    size_t prev_lemma_waiting = d_qim.numPendingLemmas();
    ++(d_qstate.getStats().d_num_quant);
    Assert(f.getKind() == FORALL);
    // register with utilities
    for (unsigned i = 0; i < d_util.size(); i++)
    {
      d_util[i]->registerQuantifier(f);
    }

    for (QuantifiersModule*& mdl : d_modules)
    {
      Trace("quant-debug") << "check ownership with " << mdl->identify()
                           << "..." << std::endl;
      mdl->checkOwnership(f);
    }
    QuantifiersModule* qm = d_qreg.getOwner(f);
    Trace("quant") << " Owner : " << (qm == nullptr ? "[none]" : qm->identify())
                   << std::endl;
    // register with each module
    for (QuantifiersModule*& mdl : d_modules)
    {
      Trace("quant-debug") << "register with " << mdl->identify() << "..."
                           << std::endl;
      mdl->registerQuantifier(f);
      // since this is context-independent, we should not add any lemmas during
      // this call
      Assert(d_qim.numPendingLemmas() == prev_lemma_waiting);
    }
    Trace("quant-debug") << "...finish." << std::endl;
    d_quants[f] = true;
    AlwaysAssert(d_qim.numPendingLemmas() == prev_lemma_waiting);
  }
}

void QuantifiersEngine::preRegisterQuantifier(Node q)
{
  NodeSet::const_iterator it = d_quants_prereg.find(q);
  if (it != d_quants_prereg.end())
  {
    return;
  }
  Trace("quant-debug") << "QuantifiersEngine : Pre-register " << q << std::endl;
  d_quants_prereg.insert(q);
  // try to reduce
  if (reduceQuantifier(q))
  {
    // if we can reduce it, nothing left to do
    return;
  }
  // ensure that it is registered
  registerQuantifierInternal(q);
  // register with each module
  for (QuantifiersModule*& mdl : d_modules)
  {
    Trace("quant-debug") << "pre-register with " << mdl->identify() << "..."
                         << std::endl;
    mdl->preRegisterQuantifier(q);
  }
  // flush the lemmas
  d_qim.doPending();
  Trace("quant-debug") << "...finish pre-register " << q << "..." << std::endl;
}

void QuantifiersEngine::assertQuantifier( Node f, bool pol ){
  if (reduceQuantifier(f))
  {
    // if we can reduce it, nothing left to do
    return;
  }
  if( !pol ){
    // do skolemization
    TrustNode lem = d_qim.getSkolemize()->process(f);
    if (!lem.isNull())
    {
      if (TraceIsOn("quantifiers-sk-debug"))
      {
        Node slem = rewrite(lem.getNode());
        Trace("quantifiers-sk-debug")
            << "Skolemize lemma : " << slem << std::endl;
      }
      d_qim.trustedLemma(lem,
                         InferenceId::QUANTIFIERS_SKOLEMIZE,
                         LemmaProperty::NEEDS_JUSTIFY);
    }
    return;
  }
  // ensure the quantified formula is registered
  registerQuantifierInternal(f);
  // assert it to each module
  d_model->assertQuantifier(f);
  for (QuantifiersModule*& mdl : d_modules)
  {
    mdl->assertNode(f);
  }
  // add term to the registry
  d_treg.addTerm(d_qreg.getInstConstantBody(f), true);
}

void QuantifiersEngine::eqNotifyNewClass(TNode t) { d_treg.addTerm(t); }

void QuantifiersEngine::markRelevant( Node q ) {
  d_model->markRelevant( q );
}

void QuantifiersEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  d_qim.getInstantiate()->getInstantiationTermVectors(q, tvecs);
}

void QuantifiersEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  d_qim.getInstantiate()->getInstantiationTermVectors(insts);
}

void QuantifiersEngine::getInstantiations(Node q, std::vector<Node>& insts)
{
  d_qim.getInstantiate()->getInstantiations(q, insts);
}

void QuantifiersEngine::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  d_qim.getInstantiate()->getInstantiatedQuantifiedFormulas(qs);
}

void QuantifiersEngine::getSkolemTermVectors(
    std::map<Node, std::vector<Node> >& sks) const
{
  d_qim.getSkolemize()->getSkolemTermVectors(sks);
}

Node QuantifiersEngine::getNameForQuant(Node q) const
{
  return d_qreg.getNameForQuant(q);
}

bool QuantifiersEngine::getNameForQuant(Node q, Node& name, bool req) const
{
  return d_qreg.getNameForQuant(q, name, req);
}

bool QuantifiersEngine::getSynthSolutions(
    std::map<Node, std::map<Node, Node> >& sol_map)
{
  return d_qmodules->d_synth_e->getSynthSolutions(sol_map);
}
void QuantifiersEngine::declarePool(Node p, const std::vector<Node>& initValue)
{
  d_treg.declarePool(p, initValue);
}

void QuantifiersEngine::declareOracleFun(Node f)
{
  if (d_qmodules->d_oracleEngine.get() == nullptr)
  {
    warning() << "Cannot declare oracle function when oracles are disabled"
              << std::endl;
    return;
  }
  d_qmodules->d_oracleEngine->declareOracleFun(f);
}
std::vector<Node> QuantifiersEngine::getOracleFuns() const
{
  if (d_qmodules->d_oracleEngine.get() == nullptr)
  {
    return {};
  }
  return d_qmodules->d_oracleEngine->getOracleFuns();
}

}  // namespace theory
}  // namespace cvc5::internal

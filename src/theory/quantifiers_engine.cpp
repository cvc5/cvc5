/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifiers engine class
 **/

#include "theory/quantifiers_engine.h"

#include "options/printer_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "smt/smt_engine_scope.h"
#include "smt/smt_statistics_registry.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/quantifiers/quantifiers_modules.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

QuantifiersEngine::QuantifiersEngine(
    quantifiers::QuantifiersState& qstate,
    quantifiers::QuantifiersInferenceManager& qim,
    ProofNodeManager* pnm)
    : d_qstate(qstate),
      d_qim(qim),
      d_te(nullptr),
      d_decManager(nullptr),
      d_qreg(),
      d_tr_trie(new inst::TriggerTrie),
      d_model(nullptr),
      d_builder(nullptr),
      d_term_util(new quantifiers::TermUtil),
      d_term_db(new quantifiers::TermDb(qstate, qim, this)),
      d_eq_query(nullptr),
      d_sygus_tdb(nullptr),
      d_quant_attr(new quantifiers::QuantAttributes),
      d_instantiate(new quantifiers::Instantiate(this, qstate, qim, pnm)),
      d_skolemize(new quantifiers::Skolemize(this, qstate, pnm)),
      d_term_enum(new quantifiers::TermEnumeration),
      d_quants_prereg(qstate.getUserContext()),
      d_quants_red(qstate.getUserContext()),
      d_ierCounter_c(qstate.getSatContext()),
      d_presolve(qstate.getUserContext(), true),
      d_presolve_in(qstate.getUserContext()),
      d_presolve_cache(qstate.getUserContext())
{
  //---- utilities
  // term util must come before the other utilities
  d_util.push_back(d_term_util.get());
  d_util.push_back(d_term_db.get());

  if (options::sygus() || options::sygusInst())
  {
    // must be constructed here since it is required for datatypes finistInit
    d_sygus_tdb.reset(new quantifiers::TermDbSygus(this, qstate, qim));
  }

  d_util.push_back(d_instantiate.get());

  Trace("quant-engine-debug") << "Initialize quantifiers engine." << std::endl;
  Trace("quant-engine-debug") << "Initialize model, mbqi : " << options::mbqiMode() << std::endl;

  //---- end utilities

  //allow theory combination to go first, once initially
  d_ierCounter = options::instWhenTcFirst() ? 0 : 1;
  d_ierCounter_c = d_ierCounter;
  d_ierCounter_lc = 0;
  d_ierCounterLastLc = 0;
  d_inst_when_phase = 1 + ( options::instWhenPhase()<1 ? 1 : options::instWhenPhase() );

  // Finite model finding requires specialized ways of building the model.
  // We require constructing the model and model builder here, since it is
  // required for initializing the CombinationEngine.
  if (options::finiteModelFind() || options::fmfBound())
  {
    Trace("quant-engine-debug") << "Initialize model engine, mbqi : " << options::mbqiMode() << " " << options::fmfBound() << std::endl;
    if (options::mbqiMode() == options::MbqiMode::FMC
        || options::mbqiMode() == options::MbqiMode::TRUST
        || options::fmfBound())
    {
      Trace("quant-engine-debug") << "...make fmc builder." << std::endl;
      d_model.reset(new quantifiers::fmcheck::FirstOrderModelFmc(
          this, qstate, "FirstOrderModelFmc"));
      d_builder.reset(new quantifiers::fmcheck::FullModelChecker(this, qstate));
    }else{
      Trace("quant-engine-debug") << "...make default model builder." << std::endl;
      d_model.reset(
          new quantifiers::FirstOrderModel(this, qstate, "FirstOrderModel"));
      d_builder.reset(new quantifiers::QModelBuilder(this, qstate));
    }
  }else{
    d_model.reset(
        new quantifiers::FirstOrderModel(this, qstate, "FirstOrderModel"));
  }
  d_eq_query.reset(new quantifiers::EqualityQueryQuantifiersEngine(
      qstate, d_term_db.get(), d_model.get()));
  d_util.insert(d_util.begin(), d_eq_query.get());
}

QuantifiersEngine::~QuantifiersEngine() {}

void QuantifiersEngine::finishInit(TheoryEngine* te, DecisionManager* dm)
{
  d_te = te;
  d_decManager = dm;
  // Initialize the modules and the utilities here.
  d_qmodules.reset(new quantifiers::QuantifiersModules);
  d_qmodules->initialize(this, d_qstate, d_qim, d_qreg, d_modules);
  if (d_qmodules->d_rel_dom.get())
  {
    d_util.push_back(d_qmodules->d_rel_dom.get());
  }
}

TheoryEngine* QuantifiersEngine::getTheoryEngine() const { return d_te; }

DecisionManager* QuantifiersEngine::getDecisionManager()
{
  return d_decManager;
}

OutputChannel& QuantifiersEngine::getOutputChannel()
{
  return d_te->theoryOf(THEORY_QUANTIFIERS)->getOutputChannel();
}
Valuation& QuantifiersEngine::getValuation() { return d_qstate.getValuation(); }

quantifiers::QuantifiersState& QuantifiersEngine::getState()
{
  return d_qstate;
}
quantifiers::QuantifiersInferenceManager&
QuantifiersEngine::getInferenceManager()
{
  return d_qim;
}
quantifiers::QModelBuilder* QuantifiersEngine::getModelBuilder() const
{
  return d_builder.get();
}
quantifiers::FirstOrderModel* QuantifiersEngine::getModel() const
{
  return d_model.get();
}
quantifiers::TermDb* QuantifiersEngine::getTermDatabase() const
{
  return d_term_db.get();
}
quantifiers::TermDbSygus* QuantifiersEngine::getTermDatabaseSygus() const
{
  return d_sygus_tdb.get();
}
quantifiers::TermUtil* QuantifiersEngine::getTermUtil() const
{
  return d_term_util.get();
}
quantifiers::QuantAttributes* QuantifiersEngine::getQuantAttributes() const
{
  return d_quant_attr.get();
}
quantifiers::Instantiate* QuantifiersEngine::getInstantiate() const
{
  return d_instantiate.get();
}
quantifiers::Skolemize* QuantifiersEngine::getSkolemize() const
{
  return d_skolemize.get();
}
quantifiers::TermEnumeration* QuantifiersEngine::getTermEnumeration() const
{
  return d_term_enum.get();
}
inst::TriggerTrie* QuantifiersEngine::getTriggerDatabase() const
{
  return d_tr_trie.get();
}

bool QuantifiersEngine::isFiniteBound(Node q, Node v) const
{
  quantifiers::BoundedIntegers* bi = d_qmodules->d_bint.get();
  if (bi && bi->isBound(q, v))
  {
    return true;
  }
  TypeNode tn = v.getType();
  if (tn.isSort() && options::finiteModelFind())
  {
    return true;
  }
  else if (d_term_enum->mayComplete(tn))
  {
    return true;
  }
  return false;
}

BoundVarType QuantifiersEngine::getBoundVarType(Node q, Node v) const
{
  quantifiers::BoundedIntegers* bi = d_qmodules->d_bint.get();
  if (bi)
  {
    return bi->getBoundVarType(q, v);
  }
  return isFiniteBound(q, v) ? BOUND_FINITE : BOUND_NONE;
}

void QuantifiersEngine::getBoundVarIndices(Node q,
                                           std::vector<unsigned>& indices) const
{
  Assert(indices.empty());
  // we take the bounded variables first
  quantifiers::BoundedIntegers* bi = d_qmodules->d_bint.get();
  if (bi)
  {
    bi->getBoundVarIndices(q, indices);
  }
  // then get the remaining ones
  for (unsigned i = 0, nvars = q[0].getNumChildren(); i < nvars; i++)
  {
    if (std::find(indices.begin(), indices.end(), i) == indices.end())
    {
      indices.push_back(i);
    }
  }
}

bool QuantifiersEngine::getBoundElements(RepSetIterator* rsi,
                                         bool initial,
                                         Node q,
                                         Node v,
                                         std::vector<Node>& elements) const
{
  quantifiers::BoundedIntegers* bi = d_qmodules->d_bint.get();
  if (bi)
  {
    return bi->getBoundElements(rsi, initial, q, v, elements);
  }
  return false;
}

void QuantifiersEngine::presolve() {
  Trace("quant-engine-proc") << "QuantifiersEngine : presolve " << std::endl;
  d_qim.clearPending();
  for( unsigned i=0; i<d_modules.size(); i++ ){
    d_modules[i]->presolve();
  }
  d_term_db->presolve();
  d_presolve = false;
  //add all terms to database
  if( options::incrementalSolving() ){
    Trace("quant-engine-proc") << "Add presolve cache " << d_presolve_cache.size() << std::endl;
    for (const Node& t : d_presolve_cache)
    {
      addTermToDatabase(t);
    }
    Trace("quant-engine-proc") << "Done add presolve cache " << std::endl;
  }
}

void QuantifiersEngine::ppNotifyAssertions(
    const std::vector<Node>& assertions) {
  Trace("quant-engine-proc")
      << "ppNotifyAssertions in QE, #assertions = " << assertions.size()
      << std::endl;
  if (options::instLevelInputOnly() && options::instMaxLevel() != -1)
  {
    for (const Node& a : assertions)
    {
      quantifiers::QuantAttributes::setInstantiationLevelAttr(a, 0);
    }
  }
  if (options::sygus())
  {
    quantifiers::SynthEngine* sye = d_qmodules->d_synth_e.get();
    for (const Node& a : assertions)
    {
      sye->preregisterAssertion(a);
    }
  }
  /* The SyGuS instantiation module needs a global view of all available
   * assertions to collect global terms that get added to each grammar.
   */
  if (options::sygusInst())
  {
    quantifiers::SygusInst* si = d_qmodules->d_sygus_inst.get();
    si->ppNotifyAssertions(assertions);
  }
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_statistics.d_time);
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
  bool setIncomplete = false;

  Trace("quant-engine-debug2") << "Quantifiers Engine call to check, level = " << e << ", needsCheck=" << needsCheck << std::endl;
  if( needsCheck ){
    //flush previous lemmas (for instance, if was interrupted), or other lemmas to process
    d_qim.doPending();
    if (d_qim.hasSentLemma())
    {
      return;
    }

    double clSet = 0;
    if( Trace.isOn("quant-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
      Trace("quant-engine") << ">>>>> Quantifiers Engine Round, effort = " << e << " <<<<<" << std::endl;
    }

    if( Trace.isOn("quant-engine-debug") ){
      Trace("quant-engine-debug") << "Quantifiers Engine check, level = " << e << std::endl;
      Trace("quant-engine-debug") << "  depth : " << d_ierCounter_c << std::endl;
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
    if( Trace.isOn("quant-engine-ee-pre") ){
      Trace("quant-engine-ee-pre") << "Equality engine (pre-inference): " << std::endl;
      debugPrintEqualityEngine( "quant-engine-ee-pre" );
    }
    if( Trace.isOn("quant-engine-assert") ){
      Trace("quant-engine-assert") << "Assertions : " << std::endl;
      getTheoryEngine()->printAssertions("quant-engine-assert");
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

    if( Trace.isOn("quant-engine-ee") ){
      Trace("quant-engine-ee") << "Equality engine : " << std::endl;
      debugPrintEqualityEngine( "quant-engine-ee" );
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
      ++(d_statistics.d_instantiation_rounds_lc);
    }else if( e==Theory::EFFORT_FULL ){
      ++(d_statistics.d_instantiation_rounds);
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
      //if we have added one, stop
      if (d_qim.hasSentLemma())
      {
        break;
      }else{
        Assert(!d_qstate.isInConflict());
        if (quant_e == QuantifiersModule::QEFFORT_CONFLICT)
        {
          if( e==Theory::EFFORT_FULL ){
            //increment if a last call happened, we are not strictly enforcing interleaving, or already were in phase
            if( d_ierCounterLastLc!=d_ierCounter_lc || !options::instWhenStrictInterleave() || d_ierCounter%d_inst_when_phase!=0 ){
              d_ierCounter = d_ierCounter + 1;
              d_ierCounterLastLc = d_ierCounter_lc;
              d_ierCounter_c = d_ierCounter_c.get() + 1;
            }
          }else if( e==Theory::EFFORT_LAST_CALL ){
            d_ierCounter_lc = d_ierCounter_lc + 1;
          }
        }
        else if (quant_e == QuantifiersModule::QEFFORT_MODEL)
        {
          if( e==Theory::EFFORT_LAST_CALL ){
            //sources of incompleteness
            for (QuantifiersUtil*& util : d_util)
            {
              if (!util->checkComplete())
              {
                Trace("quant-engine-debug") << "Set incomplete because utility "
                                            << util->identify().c_str()
                                            << " was incomplete." << std::endl;
                setIncomplete = true;
              }
            }
            if (d_qstate.isInConflict())
            {
              // we reported a conflicting lemma, should return
              setIncomplete = true;
            }
            //if we have a chance not to set incomplete
            if( !setIncomplete ){
              //check if we should set the incomplete flag
              for (QuantifiersModule*& mdl : d_modules)
              {
                if (!mdl->checkComplete())
                {
                  Trace("quant-engine-debug")
                      << "Set incomplete because module "
                      << mdl->identify().c_str() << " was incomplete."
                      << std::endl;
                  setIncomplete = true;
                  break;
                }
              }
              if( !setIncomplete ){
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
                    setIncomplete = true;
                    break;
                  }else{
                    Assert(qmd != NULL);
                    Trace("quant-engine-debug2") << "Complete for " << q << " due to " << qmd->identify().c_str() << std::endl;
                  }
                }
              }
            }
            //if setIncomplete = false, we will answer SAT, otherwise we will run at quant_e QEFFORT_LAST_CALL
            if( !setIncomplete ){
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
      bool debugInstTrace = Trace.isOn("inst-per-quant-round");
      if (options::debugInst() || debugInstTrace)
      {
        Options& sopts = smt::currentSmtEngine()->getOptions();
        std::ostream& out = *sopts.getOut();
        d_instantiate->debugPrint(out);
      }
    }
    if( Trace.isOn("quant-engine") ){
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
    if( setIncomplete ){
      Trace("quant-engine") << "Set incomplete flag." << std::endl;
      getOutputChannel().setIncomplete();
    }
    //output debug stats
    d_instantiate->debugPrintModel();
  }
}

void QuantifiersEngine::notifyCombineTheories() {
  //if allowing theory combination to happen at most once between instantiation rounds
  //d_ierCounter = 1;
  //d_ierCounterLastLc = -1;
}

bool QuantifiersEngine::reduceQuantifier( Node q ) {
  //TODO: this can be unified with preregistration: AlphaEquivalence takes ownership of reducable quants
  BoolMap::const_iterator it = d_quants_red.find( q );
  if( it==d_quants_red.end() ){
    Node lem;
    std::map< Node, Node >::iterator itr = d_quants_red_lem.find( q );
    if( itr==d_quants_red_lem.end() ){
      if (d_qmodules->d_alpha_equiv)
      {
        Trace("quant-engine-red") << "Alpha equivalence " << q << "?" << std::endl;
        //add equivalence with another quantified formula
        lem = d_qmodules->d_alpha_equiv->reduceQuantifier(q);
        if( !lem.isNull() ){
          Trace("quant-engine-red") << "...alpha equivalence success." << std::endl;
          ++(d_statistics.d_red_alpha_equiv);
        }
      }
      d_quants_red_lem[q] = lem;
    }else{
      lem = itr->second;
    }
    if( !lem.isNull() ){
      getOutputChannel().lemma( lem );
    }
    d_quants_red[q] = !lem.isNull();
    return !lem.isNull();
  }else{
    return (*it).second;
  }
}

void QuantifiersEngine::registerQuantifierInternal(Node f)
{
  std::map< Node, bool >::iterator it = d_quants.find( f );
  if( it==d_quants.end() ){
    Trace("quant") << "QuantifiersEngine : Register quantifier ";
    Trace("quant") << " : " << f << std::endl;
    size_t prev_lemma_waiting = d_qim.numPendingLemmas();
    ++(d_statistics.d_num_quant);
    Assert(f.getKind() == FORALL);
    // register with utilities
    for (unsigned i = 0; i < d_util.size(); i++)
    {
      d_util[i]->registerQuantifier(f);
    }
    // compute attributes
    d_quant_attr->computeAttributes(f);

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
    TrustNode lem = d_skolemize->process(f);
    if (!lem.isNull())
    {
      if (Trace.isOn("quantifiers-sk-debug"))
      {
        Node slem = Rewriter::rewrite(lem.getNode());
        Trace("quantifiers-sk-debug")
            << "Skolemize lemma : " << slem << std::endl;
      }
      getOutputChannel().trustedLemma(lem, LemmaProperty::NEEDS_JUSTIFY);
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
  addTermToDatabase(d_term_util->getInstConstantBody(f), true);
}

void QuantifiersEngine::addTermToDatabase(Node n, bool withinQuant)
{
  // don't add terms in quantifier bodies
  if (withinQuant && !options::registerQuantBodyTerms())
  {
    return;
  }
  if( options::incrementalSolving() ){
    if( d_presolve_in.find( n )==d_presolve_in.end() ){
      d_presolve_in.insert( n );
      d_presolve_cache.push_back( n );
    }
  }
  //only wait if we are doing incremental solving
  if( !d_presolve || !options::incrementalSolving() ){
    d_term_db->addTerm(n);
    if (d_sygus_tdb && options::sygusEvalUnfold())
    {
      d_sygus_tdb->getEvalUnfold()->registerEvalTerm(n);
    }
  }
}

void QuantifiersEngine::eqNotifyNewClass(TNode t) {
  addTermToDatabase( t );
}

void QuantifiersEngine::markRelevant( Node q ) {
  d_model->markRelevant( q );
}

bool QuantifiersEngine::getInstWhenNeedsCheck( Theory::Effort e ) {
  Trace("quant-engine-debug2") << "Get inst when needs check, counts=" << d_ierCounter << ", " << d_ierCounter_lc << std::endl;
  //determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if (options::instWhenMode() == options::InstWhenMode::FULL)
  {
    performCheck = ( e >= Theory::EFFORT_FULL );
  }
  else if (options::instWhenMode() == options::InstWhenMode::FULL_DELAY)
  {
    performCheck =
        (e >= Theory::EFFORT_FULL) && !d_qstate.getValuation().needCheck();
  }
  else if (options::instWhenMode() == options::InstWhenMode::FULL_LAST_CALL)
  {
    performCheck = ( ( e==Theory::EFFORT_FULL && d_ierCounter%d_inst_when_phase!=0 ) || e==Theory::EFFORT_LAST_CALL );
  }
  else if (options::instWhenMode()
           == options::InstWhenMode::FULL_DELAY_LAST_CALL)
  {
    performCheck =
        ((e == Theory::EFFORT_FULL && !d_qstate.getValuation().needCheck()
          && d_ierCounter % d_inst_when_phase != 0)
         || e == Theory::EFFORT_LAST_CALL);
  }
  else if (options::instWhenMode() == options::InstWhenMode::LAST_CALL)
  {
    performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }
  else
  {
    performCheck = true;
  }
  return performCheck;
}

options::UserPatMode QuantifiersEngine::getInstUserPatMode()
{
  if (options::userPatternsQuant() == options::UserPatMode::INTERLEAVE)
  {
    return d_ierCounter % 2 == 0 ? options::UserPatMode::USE
                                 : options::UserPatMode::RESORT;
  }
  else
  {
    return options::userPatternsQuant();
  }
}

void QuantifiersEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  d_instantiate->getInstantiationTermVectors(q, tvecs);
}

void QuantifiersEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  d_instantiate->getInstantiationTermVectors(insts);
}

void QuantifiersEngine::printSynthSolution( std::ostream& out ) {
  if (d_qmodules->d_synth_e)
  {
    d_qmodules->d_synth_e->printSynthSolution(out);
  }else{
    out << "Internal error : module for synth solution not found." << std::endl;
  }
}

void QuantifiersEngine::getInstantiatedQuantifiedFormulas(std::vector<Node>& qs)
{
  d_instantiate->getInstantiatedQuantifiedFormulas(qs);
}

void QuantifiersEngine::getSkolemTermVectors(
    std::map<Node, std::vector<Node> >& sks) const
{
  d_skolemize->getSkolemTermVectors(sks);
}

QuantifiersEngine::Statistics::Statistics()
    : d_time("theory::QuantifiersEngine::time"),
      d_qcf_time("theory::QuantifiersEngine::time_qcf"),
      d_ematching_time("theory::QuantifiersEngine::time_ematching"),
      d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
      d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
      d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
      d_triggers("QuantifiersEngine::Triggers", 0),
      d_simple_triggers("QuantifiersEngine::Triggers_Simple", 0),
      d_multi_triggers("QuantifiersEngine::Triggers_Multi", 0),
      d_multi_trigger_instantiations("QuantifiersEngine::Multi_Trigger_Instantiations", 0),
      d_red_alpha_equiv("QuantifiersEngine::Reductions_Alpha_Equivalence", 0),
      d_instantiations_user_patterns("QuantifiersEngine::Instantiations_User_Patterns", 0),
      d_instantiations_auto_gen("QuantifiersEngine::Instantiations_Auto_Gen", 0),
      d_instantiations_guess("QuantifiersEngine::Instantiations_Guess", 0),
      d_instantiations_qcf("QuantifiersEngine::Instantiations_Qcf_Conflict", 0),
      d_instantiations_qcf_prop("QuantifiersEngine::Instantiations_Qcf_Prop", 0),
      d_instantiations_fmf_exh("QuantifiersEngine::Instantiations_Fmf_Exh", 0),
      d_instantiations_fmf_mbqi("QuantifiersEngine::Instantiations_Fmf_Mbqi", 0),
      d_instantiations_cbqi("QuantifiersEngine::Instantiations_Cbqi", 0),
      d_instantiations_rr("QuantifiersEngine::Instantiations_Rewrite_Rules", 0)
{
  smtStatisticsRegistry()->registerStat(&d_time);
  smtStatisticsRegistry()->registerStat(&d_qcf_time);
  smtStatisticsRegistry()->registerStat(&d_ematching_time);
  smtStatisticsRegistry()->registerStat(&d_num_quant);
  smtStatisticsRegistry()->registerStat(&d_instantiation_rounds);
  smtStatisticsRegistry()->registerStat(&d_instantiation_rounds_lc);
  smtStatisticsRegistry()->registerStat(&d_triggers);
  smtStatisticsRegistry()->registerStat(&d_simple_triggers);
  smtStatisticsRegistry()->registerStat(&d_multi_triggers);
  smtStatisticsRegistry()->registerStat(&d_multi_trigger_instantiations);
  smtStatisticsRegistry()->registerStat(&d_red_alpha_equiv);
  smtStatisticsRegistry()->registerStat(&d_instantiations_user_patterns);
  smtStatisticsRegistry()->registerStat(&d_instantiations_auto_gen);
  smtStatisticsRegistry()->registerStat(&d_instantiations_guess);
  smtStatisticsRegistry()->registerStat(&d_instantiations_qcf);
  smtStatisticsRegistry()->registerStat(&d_instantiations_qcf_prop);
  smtStatisticsRegistry()->registerStat(&d_instantiations_fmf_exh);
  smtStatisticsRegistry()->registerStat(&d_instantiations_fmf_mbqi);
  smtStatisticsRegistry()->registerStat(&d_instantiations_cbqi);
  smtStatisticsRegistry()->registerStat(&d_instantiations_rr);
}

QuantifiersEngine::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_time);
  smtStatisticsRegistry()->unregisterStat(&d_qcf_time);
  smtStatisticsRegistry()->unregisterStat(&d_ematching_time);
  smtStatisticsRegistry()->unregisterStat(&d_num_quant);
  smtStatisticsRegistry()->unregisterStat(&d_instantiation_rounds);
  smtStatisticsRegistry()->unregisterStat(&d_instantiation_rounds_lc);
  smtStatisticsRegistry()->unregisterStat(&d_triggers);
  smtStatisticsRegistry()->unregisterStat(&d_simple_triggers);
  smtStatisticsRegistry()->unregisterStat(&d_multi_triggers);
  smtStatisticsRegistry()->unregisterStat(&d_multi_trigger_instantiations);
  smtStatisticsRegistry()->unregisterStat(&d_red_alpha_equiv);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_user_patterns);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_auto_gen);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_guess);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_qcf);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_qcf_prop);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_fmf_exh);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_fmf_mbqi);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_cbqi);
  smtStatisticsRegistry()->unregisterStat(&d_instantiations_rr);
}

Node QuantifiersEngine::getInternalRepresentative( Node a, Node q, int index ){
  return d_eq_query->getInternalRepresentative(a, q, index);
}

Node QuantifiersEngine::getNameForQuant(Node q) const
{
  Node name = d_quant_attr->getQuantName(q);
  if (!name.isNull())
  {
    return name;
  }
  return q;
}

bool QuantifiersEngine::getNameForQuant(Node q, Node& name, bool req) const
{
  name = getNameForQuant(q);
  // if we have a name, or we did not require one
  return name != q || !req;
}

bool QuantifiersEngine::getSynthSolutions(
    std::map<Node, std::map<Node, Node> >& sol_map)
{
  return d_qmodules->d_synth_e->getSynthSolutions(sol_map);
}

void QuantifiersEngine::debugPrintEqualityEngine( const char * c ) {
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( ee );
  std::map< TypeNode, int > typ_num;
  while( !eqcs_i.isFinished() ){
    TNode r = (*eqcs_i);
    TypeNode tr = r.getType();
    if( typ_num.find( tr )==typ_num.end() ){
      typ_num[tr] = 0;
    }
    typ_num[tr]++;
    bool firstTime = true;
    Trace(c) << "  " << r;
    Trace(c) << " : { ";
    eq::EqClassIterator eqc_i = eq::EqClassIterator( r, ee );
    while( !eqc_i.isFinished() ){
      TNode n = (*eqc_i);
      if( r!=n ){
        if( firstTime ){
          Trace(c) << std::endl;
          firstTime = false;
        }
        Trace(c) << "    " << n << std::endl;
      }
      ++eqc_i;
    }
    if( !firstTime ){ Trace(c) << "  "; }
    Trace(c) << "}" << std::endl;
    ++eqcs_i;
  }
  Trace(c) << std::endl;
  for( std::map< TypeNode, int >::iterator it = typ_num.begin(); it != typ_num.end(); ++it ){
    Trace(c) << "# eqc for " << it->first << " : " << it->second << std::endl;
  }
}

}  // namespace theory
}  // namespace CVC4

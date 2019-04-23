/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of quantifiers engine class
 **/

#include "theory/quantifiers_engine.h"

#include "options/quantifiers_options.h"
#include "options/uf_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/quantifiers/alpha_equivalence.h"
#include "theory/quantifiers/anti_skolem.h"
#include "theory/quantifiers/bv_inverter.h"
#include "theory/quantifiers/cegqi/inst_strategy_cegqi.h"
#include "theory/quantifiers/conjecture_generator.h"
#include "theory/quantifiers/ematching/inst_strategy_e_matching.h"
#include "theory/quantifiers/ematching/instantiation_engine.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/equality_infer.h"
#include "theory/quantifiers/equality_query.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/bounded_integers.h"
#include "theory/quantifiers/fmf/full_model_check.h"
#include "theory/quantifiers/fmf/model_engine.h"
#include "theory/quantifiers/inst_propagator.h"
#include "theory/quantifiers/inst_strategy_enumerative.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/local_theory_ext.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_epr.h"
#include "theory/quantifiers/quant_relevance.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/skolemize.h"
#include "theory/quantifiers/sygus/sygus_eval_unfold.h"
#include "theory/quantifiers/sygus/synth_engine.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_canonize.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_enumeration.h"
#include "theory/quantifiers/term_util.h"
#include "theory/sep/theory_sep.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

QuantifiersEngine::QuantifiersEngine(context::Context* c,
                                     context::UserContext* u,
                                     TheoryEngine* te)
    : d_te(te),
      d_eq_query(new quantifiers::EqualityQueryQuantifiersEngine(c, this)),
      d_eq_inference(nullptr),
      d_inst_prop(nullptr),
      d_tr_trie(new inst::TriggerTrie),
      d_model(nullptr),
      d_quant_rel(nullptr),
      d_rel_dom(nullptr),
      d_bv_invert(nullptr),
      d_builder(nullptr),
      d_qepr(nullptr),
      d_term_util(new quantifiers::TermUtil(this)),
      d_term_canon(new quantifiers::TermCanonize),
      d_term_db(new quantifiers::TermDb(c, u, this)),
      d_sygus_tdb(nullptr),
      d_quant_attr(new quantifiers::QuantAttributes(this)),
      d_instantiate(new quantifiers::Instantiate(this, u)),
      d_skolemize(new quantifiers::Skolemize(this, u)),
      d_term_enum(new quantifiers::TermEnumeration),
      d_alpha_equiv(nullptr),
      d_inst_engine(nullptr),
      d_model_engine(nullptr),
      d_bint(nullptr),
      d_qcf(nullptr),
      d_rr_engine(nullptr),
      d_sg_gen(nullptr),
      d_synth_e(nullptr),
      d_lte_part_inst(nullptr),
      d_fs(nullptr),
      d_i_cbqi(nullptr),
      d_qsplit(nullptr),
      d_anti_skolem(nullptr),
      d_conflict_c(c, false),
      // d_quants(u),
      d_quants_prereg(u),
      d_quants_red(u),
      d_lemmas_produced_c(u),
      d_ierCounter_c(c),
      // d_ierCounter(c),
      // d_ierCounter_lc(c),
      // d_ierCounterLastLc(c),
      d_presolve(u, true),
      d_presolve_in(u),
      d_presolve_cache(u),
      d_presolve_cache_wq(u),
      d_presolve_cache_wic(u)
{
  //---- utilities
  d_util.push_back(d_eq_query.get());
  // term util must come before the other utilities
  d_util.push_back(d_term_util.get());
  d_util.push_back(d_term_db.get());

  if (options::ceGuidedInst()) {
    d_sygus_tdb.reset(new quantifiers::TermDbSygus(c, this));
  }

  if( options::instPropagate() ){
    // notice that this option is incompatible with options::qcfAllConflict()
    d_inst_prop.reset(new quantifiers::InstPropagator(this));
    d_util.push_back(d_inst_prop.get());
    d_instantiate->addNotify(d_inst_prop->getInstantiationNotify());
  }
  
  if( options::inferArithTriggerEq() ){
    d_eq_inference.reset(new quantifiers::EqualityInference(c, false));
  }

  d_util.push_back(d_instantiate.get());

  d_curr_effort_level = QuantifiersModule::QEFFORT_NONE;
  d_conflict = false;
  d_hasAddedLemma = false;
  d_useModelEe = false;
  //don't add true lemma
  d_lemmas_produced_c[d_term_util->d_true] = true;

  Trace("quant-engine-debug") << "Initialize quantifiers engine." << std::endl;
  Trace("quant-engine-debug") << "Initialize model, mbqi : " << options::mbqiMode() << std::endl;

  if( options::relevantTriggers() ){
    d_quant_rel.reset(new quantifiers::QuantRelevance);
    d_util.push_back(d_quant_rel.get());
  }

  if( options::quantEpr() ){
    Assert( !options::incrementalSolving() );
    d_qepr.reset(new quantifiers::QuantEPR);
  }
  //---- end utilities

  //allow theory combination to go first, once initially
  d_ierCounter = options::instWhenTcFirst() ? 0 : 1;
  d_ierCounter_c = d_ierCounter;
  d_ierCounter_lc = 0;
  d_ierCounterLastLc = 0;
  d_inst_when_phase = 1 + ( options::instWhenPhase()<1 ? 1 : options::instWhenPhase() );

  bool needsBuilder = false;
  bool needsRelDom = false;
  //add quantifiers modules
  if( options::quantConflictFind() || options::quantRewriteRules() ){
    d_qcf.reset(new quantifiers::QuantConflictFind(this, c));
    d_modules.push_back(d_qcf.get());
  }
  if( options::conjectureGen() ){
    d_sg_gen.reset(new quantifiers::ConjectureGenerator(this, c));
    d_modules.push_back(d_sg_gen.get());
  }
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    d_inst_engine.reset(new quantifiers::InstantiationEngine(this));
    d_modules.push_back(d_inst_engine.get());
  }
  if( options::cbqi() ){
    d_i_cbqi.reset(new quantifiers::InstStrategyCegqi(this));
    d_modules.push_back(d_i_cbqi.get());
    if( options::cbqiBv() ){
      // if doing instantiation for BV, need the inverter class
      d_bv_invert.reset(new quantifiers::BvInverter);
    }
  }
  if( options::ceGuidedInst() ){
    d_synth_e.reset(new quantifiers::SynthEngine(this, c));
    d_modules.push_back(d_synth_e.get());
    //needsBuilder = true;
  }  
  //finite model finding
  if( options::finiteModelFind() ){
    if( options::fmfBound() ){
      d_bint.reset(new quantifiers::BoundedIntegers(c, this));
      d_modules.push_back(d_bint.get());
    }
    d_model_engine.reset(new quantifiers::ModelEngine(c, this));
    d_modules.push_back(d_model_engine.get());
    //finite model finder has special ways of building the model
    needsBuilder = true;
  }
  if( options::quantRewriteRules() ){
    d_rr_engine.reset(new quantifiers::RewriteEngine(c, this));
    d_modules.push_back(d_rr_engine.get());
  }
  if( options::ltePartialInst() ){
    d_lte_part_inst.reset(new quantifiers::LtePartialInst(this, c));
    d_modules.push_back(d_lte_part_inst.get());
  }
  if( options::quantDynamicSplit()!=quantifiers::QUANT_DSPLIT_MODE_NONE ){
    d_qsplit.reset(new quantifiers::QuantDSplit(this, c));
    d_modules.push_back(d_qsplit.get());
  }
  if( options::quantAntiSkolem() ){
    d_anti_skolem.reset(new quantifiers::QuantAntiSkolem(this));
    d_modules.push_back(d_anti_skolem.get());
  }
  if( options::quantAlphaEquiv() ){
    d_alpha_equiv.reset(new quantifiers::AlphaEquivalence(this));
  }
  //full saturation : instantiate from relevant domain, then arbitrary terms
  if( options::fullSaturateQuant() || options::fullSaturateInterleave() ){
    d_fs.reset(new quantifiers::InstStrategyEnum(this));
    d_modules.push_back(d_fs.get());
    needsRelDom = true;
  }
  
  if( needsRelDom ){
    d_rel_dom.reset(new quantifiers::RelevantDomain(this));
    d_util.push_back(d_rel_dom.get());
  }
  
  // if we require specialized ways of building the model
  if( needsBuilder ){
    Trace("quant-engine-debug") << "Initialize model engine, mbqi : " << options::mbqiMode() << " " << options::fmfBound() << std::endl;
    if (options::mbqiMode() == quantifiers::MBQI_FMC
        || options::mbqiMode() == quantifiers::MBQI_TRUST
        || options::fmfBound())
    {
      Trace("quant-engine-debug") << "...make fmc builder." << std::endl;
      d_model.reset(new quantifiers::fmcheck::FirstOrderModelFmc(
          this, c, "FirstOrderModelFmc"));
      d_builder.reset(new quantifiers::fmcheck::FullModelChecker(c, this));
    }else{
      Trace("quant-engine-debug") << "...make default model builder." << std::endl;
      d_model.reset(
          new quantifiers::FirstOrderModel(this, c, "FirstOrderModel"));
      d_builder.reset(new quantifiers::QModelBuilder(c, this));
    }
  }else{
    d_model.reset(new quantifiers::FirstOrderModel(this, c, "FirstOrderModel"));
  }
}

QuantifiersEngine::~QuantifiersEngine() {}

context::Context* QuantifiersEngine::getSatContext()
{
  return d_te->theoryOf(THEORY_QUANTIFIERS)->getSatContext();
}

context::UserContext* QuantifiersEngine::getUserContext()
{
  return d_te->theoryOf(THEORY_QUANTIFIERS)->getUserContext();
}

OutputChannel& QuantifiersEngine::getOutputChannel()
{
  return d_te->theoryOf(THEORY_QUANTIFIERS)->getOutputChannel();
}
/** get default valuation for the quantifiers engine */
Valuation& QuantifiersEngine::getValuation()
{
  return d_te->theoryOf(THEORY_QUANTIFIERS)->getValuation();
}

const LogicInfo& QuantifiersEngine::getLogicInfo() const
{
  return d_te->getLogicInfo();
}

EqualityQuery* QuantifiersEngine::getEqualityQuery() const
{
  return d_eq_query.get();
}
quantifiers::EqualityInference* QuantifiersEngine::getEqualityInference() const
{
  return d_eq_inference.get();
}
quantifiers::RelevantDomain* QuantifiersEngine::getRelevantDomain() const
{
  return d_rel_dom.get();
}
quantifiers::BvInverter* QuantifiersEngine::getBvInverter() const
{
  return d_bv_invert.get();
}
quantifiers::QuantRelevance* QuantifiersEngine::getQuantifierRelevance() const
{
  return d_quant_rel.get();
}
quantifiers::QModelBuilder* QuantifiersEngine::getModelBuilder() const
{
  return d_builder.get();
}
quantifiers::QuantEPR* QuantifiersEngine::getQuantEPR() const
{
  return d_qepr.get();
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
quantifiers::TermCanonize* QuantifiersEngine::getTermCanonize() const
{
  return d_term_canon.get();
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

quantifiers::BoundedIntegers* QuantifiersEngine::getBoundedIntegers() const
{
  return d_bint.get();
}
quantifiers::QuantConflictFind* QuantifiersEngine::getConflictFind() const
{
  return d_qcf.get();
}
quantifiers::RewriteEngine* QuantifiersEngine::getRewriteEngine() const
{
  return d_rr_engine.get();
}
quantifiers::SynthEngine* QuantifiersEngine::getSynthEngine() const
{
  return d_synth_e.get();
}
quantifiers::InstStrategyEnum* QuantifiersEngine::getInstStrategyEnum() const
{
  return d_fs.get();
}
quantifiers::InstStrategyCegqi* QuantifiersEngine::getInstStrategyCegqi() const
{
  return d_i_cbqi.get();
}

QuantifiersModule * QuantifiersEngine::getOwner( Node q ) {
  std::map< Node, QuantifiersModule * >::iterator it = d_owner.find( q );
  if( it==d_owner.end() ){
    return NULL;
  }else{
    return it->second;
  }
}

void QuantifiersEngine::setOwner( Node q, QuantifiersModule * m, int priority ) {
  QuantifiersModule * mo = getOwner( q );
  if( mo!=m ){
    if( mo!=NULL ){
      if( priority<=d_owner_priority[q] ){
        Trace("quant-warn") << "WARNING: setting owner of " << q << " to " << ( m ? m->identify() : "null" ) << ", but already has owner " << mo->identify() << " with higher priority!" << std::endl;
        return;
      }
    }
    d_owner[q] = m;
    d_owner_priority[q] = priority;
  }
}

bool QuantifiersEngine::hasOwnership( Node q, QuantifiersModule * m ) {
  QuantifiersModule * mo = getOwner( q );
  return mo==m || mo==NULL;
}

bool QuantifiersEngine::isFiniteBound( Node q, Node v ) {
  if( getBoundedIntegers() && getBoundedIntegers()->isBoundVar( q, v ) ){
    return true;
  }else{
    TypeNode tn = v.getType();
    if( tn.isSort() && options::finiteModelFind() ){
      return true;
    }
    else if (d_term_enum->mayComplete(tn))
    {
      return true;
    }
  }
  return false;
}

void QuantifiersEngine::presolve() {
  Trace("quant-engine-proc") << "QuantifiersEngine : presolve " << std::endl;
  for( unsigned i=0; i<d_modules.size(); i++ ){
    d_modules[i]->presolve();
  }
  d_term_db->presolve();
  d_presolve = false;
  //add all terms to database
  if( options::incrementalSolving() ){
    Trace("quant-engine-proc") << "Add presolve cache " << d_presolve_cache.size() << std::endl;
    for( unsigned i=0; i<d_presolve_cache.size(); i++ ){
      addTermToDatabase( d_presolve_cache[i], d_presolve_cache_wq[i], d_presolve_cache_wic[i] );
    }
    Trace("quant-engine-proc") << "Done add presolve cache " << std::endl;
  }
}

void QuantifiersEngine::ppNotifyAssertions(
    const std::vector<Node>& assertions) {
  Trace("quant-engine-proc")
      << "ppNotifyAssertions in QE, #assertions = " << assertions.size()
      << " check epr = " << (d_qepr != NULL) << std::endl;
  if ((options::instLevelInputOnly() && options::instMaxLevel() != -1) ||
      d_qepr != NULL) {
    for (unsigned i = 0; i < assertions.size(); i++) {
      if (options::instLevelInputOnly() && options::instMaxLevel() != -1) {
        quantifiers::QuantAttributes::setInstantiationLevelAttr(assertions[i],
                                                                0);
      }
      if (d_qepr != NULL) {
        d_qepr->registerAssertion(assertions[i]);
      }
    }
    if (d_qepr != NULL) {
      // must handle sources of other new constants e.g. separation logic
      // FIXME: cleanup
      sep::TheorySep* theory_sep =
          static_cast<sep::TheorySep*>(getTheoryEngine()->theoryOf(THEORY_SEP));
      theory_sep->initializeBounds();
      d_qepr->finishInit();
    }
  }
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_statistics.d_time);
  d_useModelEe = options::quantModelEe() && ( e>=Theory::EFFORT_LAST_CALL );
  // if we want to use the model's equality engine, build the model now
  if( d_useModelEe && !d_model->isBuilt() ){
    Trace("quant-engine-debug") << "Build the model." << std::endl;
    if (!d_te->getModelBuilder()->buildModel(d_model.get()))
    {
      //we are done if model building was unsuccessful
      flushLemmas();
      if( d_hasAddedLemma ){
        Trace("quant-engine-debug") << "...failed." << std::endl;
        return;
      }
    }
  }
  
  if( !getActiveEqualityEngine()->consistent() ){
    Trace("quant-engine-debug") << "Master equality engine not consistent, return." << std::endl;
    return;
  }
  if (d_conflict_c.get())
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
  bool needsCheck = !d_lemmas_waiting.empty();
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

  d_conflict = false;
  d_hasAddedLemma = false;
  bool setIncomplete = false;

  Trace("quant-engine-debug2") << "Quantifiers Engine call to check, level = " << e << ", needsCheck=" << needsCheck << std::endl;
  if( needsCheck ){
    //flush previous lemmas (for instance, if was interupted), or other lemmas to process
    flushLemmas();
    if( d_hasAddedLemma ){
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
      if( !d_lemmas_waiting.empty() ){
        Trace("quant-engine-debug") << "  lemmas waiting = " << d_lemmas_waiting.size() << std::endl;
      }
      Trace("quant-engine-debug") << "  Theory engine finished : " << !d_te->needCheck() << std::endl;
      Trace("quant-engine-debug") << "  Needs model effort : " << needsModelE << std::endl;
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
        flushLemmas();
        if( d_hasAddedLemma ){
          return;
        }else{
          //should only fail reset if added a lemma
          Assert( false );
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
    flushLemmas();
    if( d_hasAddedLemma ){
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
      d_curr_effort_level = quant_e;
      //build the model if any module requested it
      if (needsModelE == quant_e)
      {
        if (!d_model->isBuilt())
        {
          // theory engine's model builder is quantifier engine's builder if it
          // has one
          Assert(!getModelBuilder()
                 || getModelBuilder() == d_te->getModelBuilder());
          Trace("quant-engine-debug") << "Build model..." << std::endl;
          if (!d_te->getModelBuilder()->buildModel(d_model.get()))
          {
            flushLemmas();
          }
        }
        if (!d_model->isBuiltSuccess())
        {
          break;
        }
      }
      if( !d_hasAddedLemma ){
        //check each module
        for (QuantifiersModule*& mdl : qm)
        {
          Trace("quant-engine-debug") << "Check " << mdl->identify().c_str()
                                      << " at effort " << quant_e << "..."
                                      << std::endl;
          mdl->check(e, quant_e);
          if( d_conflict ){
            Trace("quant-engine-debug") << "...conflict!" << std::endl;
            break;
          }
        }
        //flush all current lemmas
        flushLemmas();
      }
      //if we have added one, stop
      if( d_hasAddedLemma ){
        break;
      }else{
        Assert( !d_conflict );
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
            if (d_conflict_c.get())
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
                  QuantifiersModule * qmd = getOwner( q );
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
                    Assert( qmd!=NULL );
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
    d_curr_effort_level = QuantifiersModule::QEFFORT_NONE;
    Trace("quant-engine-debug") << "Done check modules that needed check." << std::endl;
    if( d_hasAddedLemma ){
      d_instantiate->debugPrint();
    }
    if( Trace.isOn("quant-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("quant-engine") << "Finished quantifiers engine, total time = " << (clSet2-clSet);
      Trace("quant-engine") << ", added lemma = " << d_hasAddedLemma;
      Trace("quant-engine") << std::endl;
    }
    
    Trace("quant-engine-debug2") << "Finished quantifiers engine check." << std::endl;
  }else{
    Trace("quant-engine-debug2") << "Quantifiers Engine does not need check." << std::endl;
  }

  //SAT case
  if( e==Theory::EFFORT_LAST_CALL && !d_hasAddedLemma ){
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
      if( d_alpha_equiv ){
        Trace("quant-engine-red") << "Alpha equivalence " << q << "?" << std::endl;
        //add equivalence with another quantified formula
        lem = d_alpha_equiv->reduceQuantifier( q );
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
    unsigned prev_lemma_waiting = d_lemmas_waiting.size();
    ++(d_statistics.d_num_quant);
    Assert( f.getKind()==FORALL );
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
    QuantifiersModule* qm = getOwner(f);
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
      Assert(d_lemmas_waiting.size() == prev_lemma_waiting);
    }
    Trace("quant-debug") << "...finish." << std::endl;
    d_quants[f] = true;
    AlwaysAssert(d_lemmas_waiting.size() == prev_lemma_waiting);
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
  flushLemmas();
  Trace("quant-debug") << "...finish pre-register " << q << "..." << std::endl;
}

void QuantifiersEngine::registerPattern( std::vector<Node> & pattern) {
  for(std::vector<Node>::iterator p = pattern.begin(); p != pattern.end(); ++p){
    std::set< Node > added;
    getTermDatabase()->addTerm( *p, added );
  }
}

void QuantifiersEngine::assertQuantifier( Node f, bool pol ){
  if (reduceQuantifier(f))
  {
    // if we can reduce it, nothing left to do
    return;
  }
  if( !pol ){
    // do skolemization
    Node lem = d_skolemize->process(f);
    if (!lem.isNull())
    {
      if (Trace.isOn("quantifiers-sk-debug"))
      {
        Node slem = Rewriter::rewrite(lem);
        Trace("quantifiers-sk-debug")
            << "Skolemize lemma : " << slem << std::endl;
      }
      getOutputChannel().lemma(lem, false, true);
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

void QuantifiersEngine::addTermToDatabase( Node n, bool withinQuant, bool withinInstClosure ){
  if( options::incrementalSolving() ){
    if( d_presolve_in.find( n )==d_presolve_in.end() ){
      d_presolve_in.insert( n );
      d_presolve_cache.push_back( n );
      d_presolve_cache_wq.push_back( withinQuant );
      d_presolve_cache_wic.push_back( withinInstClosure );
    }
  }
  //only wait if we are doing incremental solving
  if( !d_presolve || !options::incrementalSolving() ){
    std::set< Node > added;
    d_term_db->addTerm(n, added, withinQuant, withinInstClosure);

    if (!withinQuant)
    {
      if (d_sygus_tdb)
      {
        d_sygus_tdb->getEvalUnfold()->registerEvalTerm(n);
      }
    }
  }
}

void QuantifiersEngine::eqNotifyNewClass(TNode t) {
  addTermToDatabase( t );
  if( d_eq_inference ){
    d_eq_inference->eqNotifyNewClass( t );
  }
}

void QuantifiersEngine::eqNotifyPreMerge(TNode t1, TNode t2) {
  if( d_eq_inference ){
    d_eq_inference->eqNotifyMerge( t1, t2 );
  }
}

void QuantifiersEngine::eqNotifyPostMerge(TNode t1, TNode t2) {

}

void QuantifiersEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  //if( d_qcf ){
  //  d_qcf->assertDisequal( t1, t2 );
  //}
}

bool QuantifiersEngine::addLemma( Node lem, bool doCache, bool doRewrite ){
  if( doCache ){
    if( doRewrite ){
      lem = Rewriter::rewrite(lem);
    }
    Trace("inst-add-debug") << "Adding lemma : " << lem << std::endl;
    BoolMap::const_iterator itp = d_lemmas_produced_c.find( lem );
    if( itp==d_lemmas_produced_c.end() || !(*itp).second ){
      //d_curr_out->lemma( lem, false, true );
      d_lemmas_produced_c[ lem ] = true;
      d_lemmas_waiting.push_back( lem );
      Trace("inst-add-debug") << "Added lemma" << std::endl;
      return true;
    }else{
      Trace("inst-add-debug") << "Duplicate." << std::endl;
      return false;
    }
  }else{
    //do not need to rewrite, will be rewritten after sending
    d_lemmas_waiting.push_back( lem );
    return true;
  }
}

bool QuantifiersEngine::removeLemma( Node lem ) {
  std::vector< Node >::iterator it = std::find( d_lemmas_waiting.begin(), d_lemmas_waiting.end(), lem );
  if( it!=d_lemmas_waiting.end() ){
    d_lemmas_waiting.erase( it, it + 1 );
    d_lemmas_produced_c[ lem ] = false;
    return true;
  }else{
    return false;
  }
}

void QuantifiersEngine::addRequirePhase( Node lit, bool req ){
  d_phase_req_waiting[lit] = req;
}

bool QuantifiersEngine::addEPRAxiom( TypeNode tn ) {
  if( d_qepr ){
    Assert( !options::incrementalSolving() );
    if( d_qepr->isEPR( tn ) && !d_qepr->hasEPRAxiom( tn ) ){
      Node lem = d_qepr->mkEPRAxiom( tn );
      Trace("quant-epr") << "EPR lemma for " << tn << " : " << lem << std::endl;
      getOutputChannel().lemma( lem );
    }
  }
  return false;
}
  
void QuantifiersEngine::markRelevant( Node q ) {
  d_model->markRelevant( q );
}

void QuantifiersEngine::setConflict() { 
  d_conflict = true; 
  d_conflict_c = true; 
}

bool QuantifiersEngine::getInstWhenNeedsCheck( Theory::Effort e ) {
  Trace("quant-engine-debug2") << "Get inst when needs check, counts=" << d_ierCounter << ", " << d_ierCounter_lc << std::endl;
  //determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if( options::instWhenMode()==quantifiers::INST_WHEN_FULL ){
    performCheck = ( e >= Theory::EFFORT_FULL );
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_FULL_DELAY ){
    performCheck = ( e >= Theory::EFFORT_FULL ) && !getTheoryEngine()->needCheck();
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_FULL_LAST_CALL ){
    performCheck = ( ( e==Theory::EFFORT_FULL && d_ierCounter%d_inst_when_phase!=0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_FULL_DELAY_LAST_CALL ){
    performCheck = ( ( e==Theory::EFFORT_FULL && !getTheoryEngine()->needCheck() && d_ierCounter%d_inst_when_phase!=0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_LAST_CALL ){
    performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }else{
    performCheck = true;
  }
  if( e==Theory::EFFORT_LAST_CALL ){
    //with bounded integers, skip every other last call,
    // since matching loops may occur with infinite quantification
    if( d_ierCounter_lc%2==0 && options::fmfBound() ){
      performCheck = false;
    }
  }
  return performCheck;
}

quantifiers::UserPatMode QuantifiersEngine::getInstUserPatMode() {
  if( options::userPatternsQuant()==quantifiers::USER_PAT_MODE_INTERLEAVE ){
    return d_ierCounter%2==0 ? quantifiers::USER_PAT_MODE_USE : quantifiers::USER_PAT_MODE_RESORT;
  }else{
    return options::userPatternsQuant();
  }
}

void QuantifiersEngine::flushLemmas(){
  if( !d_lemmas_waiting.empty() ){
    //filter based on notify classes
    if (d_instantiate->hasNotify())
    {
      unsigned prev_lem_sz = d_lemmas_waiting.size();
      d_instantiate->notifyFlushLemmas();
      if( prev_lem_sz!=d_lemmas_waiting.size() ){
        Trace("quant-engine") << "...filtered instances : " << d_lemmas_waiting.size() << " / " << prev_lem_sz << std::endl;
      }
    }
    //take default output channel if none is provided
    d_hasAddedLemma = true;
    for( unsigned i=0; i<d_lemmas_waiting.size(); i++ ){
      Trace("qe-lemma") << "Lemma : " << d_lemmas_waiting[i] << std::endl;
      getOutputChannel().lemma( d_lemmas_waiting[i], false, true );
    }
    d_lemmas_waiting.clear();
  }
  if( !d_phase_req_waiting.empty() ){
    for( std::map< Node, bool >::iterator it = d_phase_req_waiting.begin(); it != d_phase_req_waiting.end(); ++it ){
      Trace("qe-lemma") << "Require phase : " << it->first << " -> " << it->second << std::endl;
      getOutputChannel().requirePhase( it->first, it->second );
    }
    d_phase_req_waiting.clear();
  }
}

bool QuantifiersEngine::getUnsatCoreLemmas( std::vector< Node >& active_lemmas ) {
  return d_instantiate->getUnsatCoreLemmas(active_lemmas);
}

bool QuantifiersEngine::getUnsatCoreLemmas( std::vector< Node >& active_lemmas, std::map< Node, Node >& weak_imp ) {
  return d_instantiate->getUnsatCoreLemmas(active_lemmas, weak_imp);
}

void QuantifiersEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  d_instantiate->getInstantiationTermVectors(q, tvecs);
}

void QuantifiersEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  d_instantiate->getInstantiationTermVectors(insts);
}

void QuantifiersEngine::getExplanationForInstLemmas(
    const std::vector<Node>& lems,
    std::map<Node, Node>& quant,
    std::map<Node, std::vector<Node> >& tvec)
{
  d_instantiate->getExplanationForInstLemmas(lems, quant, tvec);
}

void QuantifiersEngine::printInstantiations( std::ostream& out ) {
  bool printed = false;
  // print the skolemizations
  if (d_skolemize->printSkolemization(out))
  {
    printed = true;
  }
  // print the instantiations
  if (d_instantiate->printInstantiations(out))
  {
    printed = true;
  }
  if( !printed ){
    out << "No instantiations" << std::endl;
  }
}

void QuantifiersEngine::printSynthSolution( std::ostream& out ) {
  if (d_synth_e)
  {
    d_synth_e->printSynthSolution(out);
  }else{
    out << "Internal error : module for synth solution not found." << std::endl;
  }
}

void QuantifiersEngine::getInstantiatedQuantifiedFormulas( std::vector< Node >& qs ) {
  d_instantiate->getInstantiatedQuantifiedFormulas(qs);
}

void QuantifiersEngine::getInstantiations( std::map< Node, std::vector< Node > >& insts ) {
  d_instantiate->getInstantiations(insts);
}

void QuantifiersEngine::getInstantiations( Node q, std::vector< Node >& insts  ) {
  d_instantiate->getInstantiations(q, insts);
}

Node QuantifiersEngine::getInstantiatedConjunction( Node q ) {
  return d_instantiate->getInstantiatedConjunction(q);
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

eq::EqualityEngine* QuantifiersEngine::getMasterEqualityEngine(){
  return d_te->getMasterEqualityEngine();
}

eq::EqualityEngine* QuantifiersEngine::getActiveEqualityEngine() {
  if( d_useModelEe ){
    return d_model->getEqualityEngine();
  }else{
    return d_te->getMasterEqualityEngine();
  }
}

Node QuantifiersEngine::getInternalRepresentative( Node a, Node q, int index ){
  bool prevModelEe = d_useModelEe;
  d_useModelEe = false;
  Node ret = d_eq_query->getInternalRepresentative( a, q, index );
  d_useModelEe = prevModelEe;
  return ret;
}

void QuantifiersEngine::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  d_synth_e->getSynthSolutions(sol_map);
}

void QuantifiersEngine::debugPrintEqualityEngine( const char * c ) {
  eq::EqualityEngine* ee = getActiveEqualityEngine();
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


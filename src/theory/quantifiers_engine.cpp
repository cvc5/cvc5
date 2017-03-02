/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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
#include "theory/sep/theory_sep.h"
#include "theory/quantifiers/alpha_equivalence.h"
#include "theory/quantifiers/ambqi_builder.h"
#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/conjecture_generator.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/full_model_check.h"
#include "theory/quantifiers/fun_def_engine.h"
#include "theory/quantifiers/inst_strategy_cbqi.h"
#include "theory/quantifiers/inst_strategy_e_matching.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/local_theory_ext.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/quant_equality_engine.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
#include "theory/quantifiers/quant_split.h"
#include "theory/quantifiers/anti_skolem.h"
#include "theory/quantifiers/equality_infer.h"
#include "theory/quantifiers/inst_propagator.h"
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

QuantifiersEngine::QuantifiersEngine(context::Context* c, context::UserContext* u, TheoryEngine* te):
    d_te( te ),
    d_conflict_c(c, false),
    //d_quants(u),
    d_quants_red(u),
    d_lemmas_produced_c(u),
    d_skolemized(u),
    d_ierCounter_c(c),
    //d_ierCounter(c),
    //d_ierCounter_lc(c),
    //d_ierCounterLastLc(c),
    d_presolve(u, true),
    d_presolve_in(u),
    d_presolve_cache(u),
    d_presolve_cache_wq(u),
    d_presolve_cache_wic(u){
  //utilities
  d_eq_query = new EqualityQueryQuantifiersEngine( c, this );
  d_util.push_back( d_eq_query );

  d_term_db = new quantifiers::TermDb( c, u, this );
  d_util.push_back( d_term_db );

  if( options::instPropagate() ){
    d_inst_prop = new quantifiers::InstPropagator( this );
    d_util.push_back( d_inst_prop );
    d_inst_notify.push_back( d_inst_prop->getInstantiationNotify() );
  }else{
    d_inst_prop = NULL;
  }

  d_tr_trie = new inst::TriggerTrie;
  d_curr_effort_level = QEFFORT_NONE;
  d_conflict = false;
  d_hasAddedLemma = false;
  //don't add true lemma
  d_lemmas_produced_c[d_term_db->d_true] = true;

  Trace("quant-engine-debug") << "Initialize quantifiers engine." << std::endl;
  Trace("quant-engine-debug") << "Initialize model, mbqi : " << options::mbqiMode() << std::endl;

  //the model object
  if( options::mbqiMode()==quantifiers::MBQI_FMC ||
      options::mbqiMode()==quantifiers::MBQI_FMC_INTERVAL || options::fmfBound() ||
      options::mbqiMode()==quantifiers::MBQI_TRUST ){
    d_model = new quantifiers::fmcheck::FirstOrderModelFmc( this, c, "FirstOrderModelFmc" );
  }else if( options::mbqiMode()==quantifiers::MBQI_ABS ){
    d_model = new quantifiers::FirstOrderModelAbs( this, c, "FirstOrderModelAbs" );
  }else{
    d_model = new quantifiers::FirstOrderModelIG( this, c, "FirstOrderModelIG" );
  }
  if( options::relevantTriggers() ){
    d_quant_rel = new QuantRelevance( false );
  }else{
    d_quant_rel = NULL;
  }

  if( options::quantEpr() ){
    Assert( !options::incrementalSolving() );
    d_qepr = new QuantEPR;
  }else{
    d_qepr = NULL;
  }


  d_qcf = NULL;
  d_sg_gen = NULL;
  d_inst_engine = NULL;
  d_i_cbqi = NULL;
  d_qsplit = NULL;
  d_anti_skolem = NULL;
  d_model_engine = NULL;
  d_bint = NULL;
  d_rr_engine = NULL;
  d_ceg_inst = NULL;
  d_lte_part_inst = NULL;
  d_alpha_equiv = NULL;
  d_fun_def_engine = NULL;
  d_uee = NULL;
  d_fs = NULL;
  d_rel_dom = NULL;
  d_builder = NULL;

  d_total_inst_count_debug = 0;
  //allow theory combination to go first, once initially
  d_ierCounter = options::instWhenTcFirst() ? 0 : 1;
  d_ierCounter_c = d_ierCounter;
  d_ierCounter_lc = 0;
  d_ierCounterLastLc = 0;
  d_inst_when_phase = 1 + ( options::instWhenPhase()<1 ? 1 : options::instWhenPhase() );
}

QuantifiersEngine::~QuantifiersEngine(){
  for(std::map< Node, inst::CDInstMatchTrie* >::iterator
      i = d_c_inst_match_trie.begin(), iend = d_c_inst_match_trie.end();
      i != iend; ++i)
  {
    delete (*i).second;
  }
  d_c_inst_match_trie.clear();

  delete d_alpha_equiv;
  delete d_builder;
  delete d_qepr;
  delete d_rr_engine;
  delete d_bint;
  delete d_model_engine;
  delete d_inst_engine;
  delete d_qcf;
  delete d_quant_rel;
  delete d_rel_dom;
  delete d_model;
  delete d_tr_trie;
  delete d_term_db;
  delete d_eq_query;
  delete d_sg_gen;
  delete d_ceg_inst;
  delete d_lte_part_inst;
  delete d_fun_def_engine;
  delete d_uee;
  delete d_fs;
  delete d_i_cbqi;
  delete d_qsplit;
  delete d_anti_skolem;
  delete d_inst_prop;
}

EqualityQueryQuantifiersEngine* QuantifiersEngine::getEqualityQuery() {
  return d_eq_query;
}

context::Context* QuantifiersEngine::getSatContext(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getSatContext();
}

context::UserContext* QuantifiersEngine::getUserContext(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getUserContext();
}

OutputChannel& QuantifiersEngine::getOutputChannel(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getOutputChannel();
}
/** get default valuation for the quantifiers engine */
Valuation& QuantifiersEngine::getValuation(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getValuation();
}

void QuantifiersEngine::finishInit(){
  context::Context * c = getSatContext();
  Trace("quant-engine-debug") << "QuantifiersEngine : finishInit " << std::endl;
  bool needsBuilder = false;
  bool needsRelDom = false;
  //add quantifiers modules
  if( options::quantConflictFind() || options::quantRewriteRules() ){
    d_qcf = new quantifiers::QuantConflictFind( this, c);
    d_modules.push_back( d_qcf );
  }
  if( options::conjectureGen() ){
    d_sg_gen = new quantifiers::ConjectureGenerator( this, c );
    d_modules.push_back( d_sg_gen );
  }
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    d_inst_engine = new quantifiers::InstantiationEngine( this );
    d_modules.push_back(  d_inst_engine );
  }
  if( options::cbqi() ){
    d_i_cbqi = new quantifiers::InstStrategyCegqi( this );
    d_modules.push_back( d_i_cbqi );
    if( options::cbqiModel() ){
      needsBuilder = true;
    }
  }
  if( options::ceGuidedInst() ){
    d_ceg_inst = new quantifiers::CegInstantiation( this, c );
    d_modules.push_back( d_ceg_inst );
    needsBuilder = true;
  }  
  //finite model finding
  if( options::finiteModelFind() ){
    if( options::fmfBound() ){
      d_bint = new quantifiers::BoundedIntegers( c, this );
      d_modules.push_back( d_bint );
    }
    d_model_engine = new quantifiers::ModelEngine( c, this );
    d_modules.push_back( d_model_engine );
    needsBuilder = true;
  }
  if( options::quantRewriteRules() ){
    d_rr_engine = new quantifiers::RewriteEngine( c, this );
    d_modules.push_back(d_rr_engine);
  }
  if( options::ltePartialInst() ){
    d_lte_part_inst = new quantifiers::LtePartialInst( this, c );
    d_modules.push_back( d_lte_part_inst );
  }
  if( options::quantDynamicSplit()!=quantifiers::QUANT_DSPLIT_MODE_NONE ){
    d_qsplit = new quantifiers::QuantDSplit( this, c );
    d_modules.push_back( d_qsplit );
  }
  if( options::quantAntiSkolem() ){
    d_anti_skolem = new quantifiers::QuantAntiSkolem( this );
    d_modules.push_back( d_anti_skolem );
  }
  if( options::quantAlphaEquiv() ){
    d_alpha_equiv = new quantifiers::AlphaEquivalence( this );
  }
  //if( options::funDefs() ){
  //  d_fun_def_engine = new quantifiers::FunDefEngine( this, c );
  //  d_modules.push_back( d_fun_def_engine );
  //}
  if( options::quantEqualityEngine() ){
    d_uee = new quantifiers::QuantEqualityEngine( this, c );
    d_modules.push_back( d_uee );
  }
  //full saturation : instantiate from relevant domain, then arbitrary terms
  if( options::fullSaturateQuant() || options::fullSaturateInst() ){
    d_fs = new quantifiers::FullSaturation( this );
    d_modules.push_back( d_fs );
    needsRelDom = true;
  }
 
  if( needsRelDom ){
    d_rel_dom = new quantifiers::RelevantDomain( this, d_model );
    d_util.push_back( d_rel_dom );
  }

  if( needsBuilder ){
    Trace("quant-engine-debug") << "Initialize model engine, mbqi : " << options::mbqiMode() << " " << options::fmfBound() << std::endl;
    if( options::mbqiMode()==quantifiers::MBQI_FMC || options::mbqiMode()==quantifiers::MBQI_FMC_INTERVAL ||
        options::mbqiMode()==quantifiers::MBQI_TRUST || options::fmfBound() ){
      Trace("quant-engine-debug") << "...make fmc builder." << std::endl;
      d_builder = new quantifiers::fmcheck::FullModelChecker( c, this );
    }else if( options::mbqiMode()==quantifiers::MBQI_ABS ){
      Trace("quant-engine-debug") << "...make abs mbqi builder." << std::endl;
      d_builder = new quantifiers::AbsMbqiBuilder( c, this );
    }else{
      Trace("quant-engine-debug") << "...make default model builder." << std::endl;
      d_builder = new quantifiers::QModelBuilderDefault( c, this );
    }
  }

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
    }else if( getTermDatabase()->mayComplete( tn ) ){
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

void QuantifiersEngine::ppNotifyAssertions( std::vector< Node >& assertions ) {
  Trace("quant-engine-proc") << "ppNotifyAssertions in QE, #assertions = " << assertions.size() << " check epr = " << (d_qepr!=NULL) << std::endl;
  if( ( options::instLevelInputOnly() && options::instMaxLevel()!=-1 ) || d_qepr!=NULL ){
    for( unsigned i=0; i<assertions.size(); i++ ) {
      if( options::instLevelInputOnly() && options::instMaxLevel()!=-1 ){
        setInstantiationLevelAttr( assertions[i], 0 );
      }
      if( d_qepr!=NULL ){
        d_qepr->registerAssertion( assertions[i] );
      }
    }
    if( d_qepr!=NULL ){
      //must handle sources of other new constants e.g. separation logic
      //FIXME: cleanup
      ((sep::TheorySep*)getTheoryEngine()->theoryOf( THEORY_SEP ))->initializeBounds();
      d_qepr->finishInit(); 
    }
  }
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_statistics.d_time);
  if( !getMasterEqualityEngine()->consistent() ){
    Trace("quant-engine-debug") << "Master equality engine not consistent, return." << std::endl;
    return;
  }
  bool needsCheck = !d_lemmas_waiting.empty();
  unsigned needsModelE = QEFFORT_NONE;
  std::vector< QuantifiersModule* > qm;
  if( d_model->checkNeeded() ){
    needsCheck = needsCheck || e>=Theory::EFFORT_LAST_CALL;  //always need to check at or above last call
    for( unsigned i=0; i<d_modules.size(); i++ ){
      if( d_modules[i]->needsCheck( e ) ){
        qm.push_back( d_modules[i] );
        needsCheck = true;
        //can only request model at last call since theory combination can find inconsistencies
        if( e>=Theory::EFFORT_LAST_CALL ){
          unsigned me = d_modules[i]->needsModel( e );
          needsModelE = me<needsModelE ? me : needsModelE;
        }
      }
    }
  }

  d_conflict = false;
  d_hasAddedLemma = false;
  bool setIncomplete = false;
  bool usedModelBuilder = false;

  Trace("quant-engine-debug2") << "Quantifiers Engine call to check, level = " << e << ", needsCheck=" << needsCheck << std::endl;
  if( needsCheck ){
    //this will fail if a set of instances is marked as a conflict, but is not
    Assert( !d_conflict_c.get() );
    //flush previous lemmas (for instance, if was interupted), or other lemmas to process
    flushLemmas();
    if( d_hasAddedLemma ){
      return;
    }
    if( !d_recorded_inst.empty() ){
      Trace("quant-engine-debug") << "Removing " << d_recorded_inst.size() << " instantiations..." << std::endl;
      //remove explicitly recorded instantiations
      for( unsigned i=0; i<d_recorded_inst.size(); i++ ){
        removeInstantiationInternal( d_recorded_inst[i].first, d_recorded_inst[i].second );
      } 
      d_recorded_inst.clear();
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
    for( unsigned i=0; i<d_util.size(); i++ ){
      Trace("quant-engine-debug2") << "Reset " << d_util[i]->identify().c_str() << "..." << std::endl;
      if( !d_util[i]->reset( e ) ){
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
    for( unsigned i=0; i<d_modules.size(); i++ ){
      Trace("quant-engine-debug2") << "Reset " << d_modules[i]->identify().c_str() << std::endl;
      d_modules[i]->reset_round( e );
    }
    Trace("quant-engine-debug") << "Done resetting all modules." << std::endl;
    //reset may have added lemmas
    flushLemmas();
    if( d_hasAddedLemma ){
      return;
    }

    if( e==Theory::EFFORT_LAST_CALL ){
      //if effort is last call, try to minimize model first
      //uf::StrongSolverTheoryUF * ufss = ((uf::TheoryUF*)getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver();
      //if( ufss && !ufss->minimize() ){ return; }
      ++(d_statistics.d_instantiation_rounds_lc);
    }else if( e==Theory::EFFORT_FULL ){
      ++(d_statistics.d_instantiation_rounds);
    }
    Trace("quant-engine-debug") << "Check modules that needed check..." << std::endl;
    for( unsigned quant_e = QEFFORT_CONFLICT; quant_e<=QEFFORT_LAST_CALL; quant_e++ ){
      d_curr_effort_level = quant_e;
      bool success = true;
      //build the model if any module requested it
      if( needsModelE==quant_e ){
        Assert( d_builder!=NULL );
        Trace("quant-engine-debug") << "Build model..." << std::endl;
        usedModelBuilder = true;
        d_builder->d_addedLemmas = 0;
        d_builder->buildModel( d_model, false );
        //we are done if model building was unsuccessful
        if( d_builder->d_addedLemmas>0 ){
          success = false;
        }
      }
      if( success ){
        //check each module
        for( unsigned i=0; i<qm.size(); i++ ){
          Trace("quant-engine-debug") << "Check " << qm[i]->identify().c_str() << " at effort " << quant_e << "..." << std::endl;
          qm[i]->check( e, quant_e );
          if( d_conflict ){
            Trace("quant-engine-debug") << "...conflict!" << std::endl;
            break;
          }
        }
      }
      //flush all current lemmas
      flushLemmas();
      //if we have added one, stop
      if( d_hasAddedLemma ){
        break;
      }else{
        Assert( !d_conflict );
        if( quant_e==QEFFORT_CONFLICT ){
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
        }else if( quant_e==QEFFORT_MODEL ){
          if( e==Theory::EFFORT_LAST_CALL ){
            //sources of incompleteness
            if( !d_recorded_inst.empty() ){
              Trace("quant-engine-debug") << "Set incomplete due to recorded instantiations." << std::endl;
              setIncomplete = true;
            }
            //if we have a chance not to set incomplete
            if( !setIncomplete ){
              setIncomplete = false;
              //check if we should set the incomplete flag
              for( unsigned i=0; i<d_modules.size(); i++ ){
                if( !d_modules[i]->checkComplete() ){
                  Trace("quant-engine-debug") << "Set incomplete because " << d_modules[i]->identify().c_str() << " was incomplete." << std::endl;
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
    d_curr_effort_level = QEFFORT_NONE;
    Trace("quant-engine-debug") << "Done check modules that needed check." << std::endl;
    if( d_hasAddedLemma ){
      //debug information
      if( Trace.isOn("inst-per-quant-round") ){
        for( std::map< Node, int >::iterator it = d_temp_inst_debug.begin(); it != d_temp_inst_debug.end(); ++it ){
          Trace("inst-per-quant-round") << " * " << it->second << " for " << it->first << std::endl;
          d_temp_inst_debug[it->first] = 0;
        }
      }
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
    if( options::produceModels() ){
      if( usedModelBuilder ){
        Trace("quant-engine-debug") << "Build completed model..." << std::endl;
        d_builder->buildModel( d_model, true );
      }else if( !d_model->isModelSet() ){
        //use default model builder when no module built the model
        Trace("quant-engine-debug") << "Build the model..." << std::endl;
        d_te->getModelBuilder()->buildModel( d_model, true );
        Trace("quant-engine-debug") << "Done building the model." << std::endl;
      }
    }
    if( setIncomplete ){
      Trace("quant-engine") << "Set incomplete flag." << std::endl;
      getOutputChannel().setIncomplete();
    }
    //output debug stats
    if( Trace.isOn("inst-per-quant") ){
      for( std::map< Node, int >::iterator it = d_total_inst_debug.begin(); it != d_total_inst_debug.end(); ++it ){
        Trace("inst-per-quant") << " * " << it->second << " for " << it->first << std::endl;
      }
    }
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

bool QuantifiersEngine::registerQuantifier( Node f ){
  std::map< Node, bool >::iterator it = d_quants.find( f );
  if( it==d_quants.end() ){
    Trace("quant") << "QuantifiersEngine : Register quantifier ";
    Trace("quant") << " : " << f << std::endl;
    ++(d_statistics.d_num_quant);
    Assert( f.getKind()==FORALL );

    //check whether we should apply a reduction
    if( reduceQuantifier( f ) ){
      Trace("quant") << "...reduced." << std::endl;
      d_quants[f] = false;
      return false;
    }else{
      //make instantiation constants for f
      d_term_db->makeInstantiationConstantsFor( f );
      d_term_db->computeAttributes( f );
      for( unsigned i=0; i<d_modules.size(); i++ ){
        Trace("quant-debug") << "pre-register with " << d_modules[i]->identify() << "..." << std::endl;
        d_modules[i]->preRegisterQuantifier( f );
      }
      QuantifiersModule * qm = getOwner( f );
      if( qm!=NULL ){
        Trace("quant") << "   Owner : " << qm->identify() << std::endl;
      }
      //register with quantifier relevance
      if( d_quant_rel ){
        d_quant_rel->registerQuantifier( f );
      }
      //register with each module
      for( unsigned i=0; i<d_modules.size(); i++ ){
        Trace("quant-debug") << "register with " << d_modules[i]->identify() << "..." << std::endl;
        d_modules[i]->registerQuantifier( f );
      }
      //TODO: remove this
      Node ceBody = d_term_db->getInstConstantBody( f );
      //also register it with the strong solver
      //if( options::finiteModelFind() ){
      //  ((uf::TheoryUF*)d_te->theoryOf( THEORY_UF ))->getStrongSolver()->registerQuantifier( f );
      //}
      Trace("quant-debug")  << "...finish." << std::endl;
      d_quants[f] = true;
      return true;
    }
  }else{
    return (*it).second;
  }
}

void QuantifiersEngine::registerPattern( std::vector<Node> & pattern) {
  for(std::vector<Node>::iterator p = pattern.begin(); p != pattern.end(); ++p){
    std::set< Node > added;
    getTermDatabase()->addTerm( *p, added );
  }
}

void QuantifiersEngine::assertQuantifier( Node f, bool pol ){
  if( !pol ){
    //if not reduced
    if( !reduceQuantifier( f ) ){
      //do skolemization
      if( d_skolemized.find( f )==d_skolemized.end() ){
        Node body = d_term_db->getSkolemizedBody( f );
        NodeBuilder<> nb(kind::OR);
        nb << f << body.notNode();
        Node lem = nb;
        if( Trace.isOn("quantifiers-sk-debug") ){
          Node slem = Rewriter::rewrite( lem );
          Trace("quantifiers-sk-debug") << "Skolemize lemma : " << slem << std::endl;
        }
        getOutputChannel().lemma( lem, false, true );
        d_skolemized[f] = true;
      }
    }
  }else{
    //assert to modules TODO : also for !pol?
    //register the quantifier, assert it to each module
    if( registerQuantifier( f ) ){
      d_model->assertQuantifier( f );
      for( unsigned i=0; i<d_modules.size(); i++ ){
        d_modules[i]->assertNode( f );
      }
      addTermToDatabase( d_term_db->getInstConstantBody( f ), true );
    }
  }
}

void QuantifiersEngine::propagate( Theory::Effort level ){
  CodeTimer codeTimer(d_statistics.d_time);

  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->propagate( level );
  }
}

Node QuantifiersEngine::getNextDecisionRequest( unsigned& priority ){
  unsigned min_priority = 0;
  Node dec;  
  for( unsigned i=0; i<d_modules.size(); i++ ){
    Node n = d_modules[i]->getNextDecisionRequest( priority );
    if( !n.isNull() && ( dec.isNull() || priority<min_priority ) ){
      dec = n;
      min_priority = priority;
    }
  }
  return dec;
}

quantifiers::TermDbSygus* QuantifiersEngine::getTermDatabaseSygus() {
  return getTermDatabase()->getTermDatabaseSygus();
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
    getTermDatabase()->addTerm( n, added, withinQuant, withinInstClosure );
    
    //added contains also the Node that just have been asserted in this branch
    if( d_quant_rel ){
      for( std::set< Node >::iterator i=added.begin(), end=added.end(); i!=end; i++ ){
        if( !withinQuant ){
          d_quant_rel->setRelevance( i->getOperator(), 0 );
        }
      }
    }
  }
}

void QuantifiersEngine::eqNotifyNewClass(TNode t) {
  addTermToDatabase( t );
  if( d_eq_query->getEqualityInference() ){
    d_eq_query->getEqualityInference()->eqNotifyNewClass( t );
  }
}

void QuantifiersEngine::eqNotifyPreMerge(TNode t1, TNode t2) {
  if( d_eq_query->getEqualityInference() ){
    d_eq_query->getEqualityInference()->eqNotifyMerge( t1, t2 );
  }
}

void QuantifiersEngine::eqNotifyPostMerge(TNode t1, TNode t2) {

}

void QuantifiersEngine::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
  //if( d_qcf ){
  //  d_qcf->assertDisequal( t1, t2 );
  //}
}

void QuantifiersEngine::computeTermVector( Node f, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node n = m.get( i );
    if( !n.isNull() ){
      vars.push_back( f[0][i] );
      terms.push_back( n );
    }
  }
}


bool QuantifiersEngine::recordInstantiationInternal( Node q, std::vector< Node >& terms, bool modEq, bool addedLem ) {
  if( !addedLem ){
    //record the instantiation for deletion later
    d_recorded_inst.push_back( std::pair< Node, std::vector< Node > >( q, terms ) );
  }
  if( options::incrementalSolving() ){
    Trace("inst-add-debug") << "Adding into context-dependent inst trie, modEq = " << modEq << std::endl;
    inst::CDInstMatchTrie* imt;
    std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.find( q );
    if( it!=d_c_inst_match_trie.end() ){
      imt = it->second;
    }else{
      imt = new CDInstMatchTrie( getUserContext() );
      d_c_inst_match_trie[q] = imt;
    }
    return imt->addInstMatch( this, q, terms, getUserContext(), modEq );
  }else{
    Trace("inst-add-debug") << "Adding into inst trie" << std::endl;
    return d_inst_match_trie[q].addInstMatch( this, q, terms, modEq );
  }
}

bool QuantifiersEngine::removeInstantiationInternal( Node q, std::vector< Node >& terms ) {
  if( options::incrementalSolving() ){
    std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.find( q );
    if( it!=d_c_inst_match_trie.end() ){
      return it->second->removeInstMatch( this, q, terms );
    }else{
      return false;
    }
  }else{
    return d_inst_match_trie[q].removeInstMatch( this, q, terms );
  }
}

void QuantifiersEngine::setInstantiationLevelAttr( Node n, Node qn, uint64_t level ){
  Trace("inst-level-debug2") << "IL : " << n << " " << qn << " " << level << std::endl;
  //if not from the vector of terms we instantiatied
  if( qn.getKind()!=BOUND_VARIABLE && n!=qn ){
    //if this is a new term, without an instantiation level
    if( !n.hasAttribute(InstLevelAttribute()) ){
      InstLevelAttribute ila;
      n.setAttribute(ila,level);
      Trace("inst-level-debug") << "Set instantiation level " << n << " to " << level << std::endl;
      Assert( n.getNumChildren()==qn.getNumChildren() );
      for( unsigned i=0; i<n.getNumChildren(); i++ ){
        setInstantiationLevelAttr( n[i], qn[i], level );
      }
    }
  }
}

void QuantifiersEngine::setInstantiationLevelAttr( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
    Trace("inst-level-debug") << "Set instantiation level " << n << " to " << level << std::endl;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      setInstantiationLevelAttr( n[i], level );
    }
  }
}

Node QuantifiersEngine::getSubstitute( Node n, std::vector< Node >& terms ){
  if( n.getKind()==INST_CONSTANT ){
    Debug("check-inst") << "Substitute inst constant : " << n << std::endl;
    return terms[n.getAttribute(InstVarNumAttribute())];
  }else{
    //if( !quantifiers::TermDb::hasInstConstAttr( n ) ){
      //Debug("check-inst") << "No inst const attr : " << n << std::endl;
      //return n;
    //}else{
      //Debug("check-inst") << "Recurse on : " << n << std::endl;
    std::vector< Node > cc;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      cc.push_back( n.getOperator() );
    }
    bool changed = false;
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      Node c = getSubstitute( n[i], terms );
      cc.push_back( c );
      changed = changed || c!=n[i];
    }
    if( changed ){
      Node ret = NodeManager::currentNM()->mkNode( n.getKind(), cc );
      return ret;
    }else{
      return n;
    }
  }
}


Node QuantifiersEngine::getInstantiation( Node q, std::vector< Node >& vars, std::vector< Node >& terms, bool doVts ){
  Node body;
  Assert( vars.size()==terms.size() );
  //process partial instantiation if necessary
  if( q[0].getNumChildren()!=vars.size() ){
    body = q[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
    std::vector< Node > uninst_vars;
    //doing a partial instantiation, must add quantifier for all uninstantiated variables
    for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
      if( std::find( vars.begin(), vars.end(), q[0][i] )==vars.end() ){
        uninst_vars.push_back( q[0][i] );
      }
    }
    Trace("partial-inst") << "Partially instantiating with " << vars.size() << " / " << q[0].getNumChildren() << " for " << q << std::endl;
    Assert( !uninst_vars.empty() );
    Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, uninst_vars );
    body = NodeManager::currentNM()->mkNode( FORALL, bvl, body );
    Trace("partial-inst") << "Partial instantiation : " << q << std::endl;
    Trace("partial-inst") << "                      : " << body << std::endl;
  }else{
    if( options::cbqi() ){
      body = q[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
    }else{
      //do optimized version
      Node icb = d_term_db->getInstConstantBody( q );
      body = getSubstitute( icb, terms );
      if( Debug.isOn("check-inst") ){
        Node body2 = q[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
        if( body!=body2 ){
          Debug("check-inst") << "Substitution is wrong : " << body << " " << body2 << std::endl;
        }
      }
    }
  }
  if( doVts ){
    //do virtual term substitution
    body = Rewriter::rewrite( body );
    Trace("quant-vts-debug") << "Rewrite vts symbols in " << body << std::endl;
    Node body_r = d_term_db->rewriteVtsSymbols( body );
    Trace("quant-vts-debug") << "            ...result: " << body_r << std::endl;
    body = body_r;
  }
  return body;
}

Node QuantifiersEngine::getInstantiation( Node q, InstMatch& m, bool doVts ){
  std::vector< Node > vars;
  std::vector< Node > terms;
  computeTermVector( q, m, vars, terms );
  return getInstantiation( q, vars, terms, doVts );
}

Node QuantifiersEngine::getInstantiation( Node q, std::vector< Node >& terms, bool doVts ) {
  Assert( d_term_db->d_vars.find( q )!=d_term_db->d_vars.end() );
  return getInstantiation( q, d_term_db->d_vars[q], terms, doVts );
}

/*
bool QuantifiersEngine::existsInstantiation( Node f, InstMatch& m, bool modEq ){
  if( options::incrementalSolving() ){
    if( d_c_inst_match_trie.find( f )!=d_c_inst_match_trie.end() ){
      if( d_c_inst_match_trie[f]->existsInstMatch( this, f, m, getUserContext(), modEq ) ){
        return true;
      }
    }
  }else{
    if( d_inst_match_trie.find( f )!=d_inst_match_trie.end() ){
      if( d_inst_match_trie[f].existsInstMatch( this, f, m, modEq ) ){
        return true;
      }
    }
  }
  return false;
}
*/

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

bool QuantifiersEngine::addInstantiation( Node q, InstMatch& m, bool mkRep, bool modEq, bool doVts ){
  std::vector< Node > terms;
  m.getTerms( q, terms );
  return addInstantiation( q, terms, mkRep, modEq, doVts );
}

bool QuantifiersEngine::addInstantiation( Node q, std::vector< Node >& terms, bool mkRep, bool modEq, bool doVts ) {
  // For resource-limiting (also does a time check).
  getOutputChannel().safePoint(options::quantifierStep());
  Assert( !d_conflict );
  Assert( terms.size()==q[0].getNumChildren() );
  Trace("inst-add-debug") << "For quantified formula " << q << ", add instantiation: " << std::endl;
  std::vector< Node > rlv_cond;
  for( unsigned i=0; i<terms.size(); i++ ){
    Trace("inst-add-debug") << "  " << q[0][i];
    Trace("inst-add-debug2") << " -> " << terms[i];
    if( terms[i].isNull() ){
      terms[i] = d_term_db->getModelBasisTerm( q[0][i].getType() );
    }
    if( mkRep ){
      //pick the best possible representative for instantiation, based on past use and simplicity of term
      terms[i] = d_eq_query->getInternalRepresentative( terms[i], q, i );
    }else{
      //ensure the type is correct
      terms[i] = quantifiers::TermDb::ensureType( terms[i], q[0][i].getType() );
    }
    Trace("inst-add-debug") << " -> " << terms[i] << std::endl;
    if( terms[i].isNull() ){
      Trace("inst-add-debug") << " --> Failed to make term vector, due to term/type restrictions." << std::endl;
      return false;
    }else{
      //get relevancy conditions
      if( options::instRelevantCond() ){
        quantifiers::TermDb::getRelevancyCondition( terms[i], rlv_cond );
      }
    }
#ifdef CVC4_ASSERTIONS
    bool bad_inst = false;
    if( quantifiers::TermDb::containsUninterpretedConstant( terms[i] ) ){
      Trace("inst") << "***& inst contains uninterpreted constant : " << terms[i] << std::endl;
      bad_inst = true;
    }else if( !terms[i].getType().isSubtypeOf( q[0][i].getType() ) ){
      Trace("inst") << "***& inst bad type : " << terms[i] << " " << terms[i].getType() << "/" << q[0][i].getType() << std::endl;
      bad_inst = true;
    }else if( options::cbqi() ){
      Node icf = quantifiers::TermDb::getInstConstAttr(terms[i]);
      if( !icf.isNull() ){
        if( icf==q ){
          Trace("inst") << "***& inst contains inst constant attr : " << terms[i] << std::endl;
          bad_inst = true;
        }else if( quantifiers::TermDb::containsTerms( terms[i], d_term_db->d_inst_constants[q] ) ){
          Trace("inst") << "***& inst contains inst constants : " << terms[i] << std::endl;
          bad_inst = true;
        }
      }
    }
    //this assertion is critical to soundness
    if( bad_inst ){
      Trace("inst")<< "***& Bad Instantiate " << q << " with " << std::endl;
      for( unsigned j=0; j<terms.size(); j++ ){
        Trace("inst") << "   " << terms[j] << std::endl;
      }
      Assert( false );
    }
#endif
  }

  //check based on instantiation level
  if( options::instMaxLevel()!=-1 || options::lteRestrictInstClosure() ){
    for( unsigned i=0; i<terms.size(); i++ ){
      if( !d_term_db->isTermEligibleForInstantiation( terms[i], q, true ) ){
        return false;
      }
    }
  }

  //check for positive entailment
  if( options::instNoEntail() ){
    //TODO: check consistency of equality engine (if not aborting on utility's reset)
    std::map< TNode, TNode > subs;
    for( unsigned i=0; i<terms.size(); i++ ){
      subs[q[0][i]] = terms[i];
    }
    if( d_term_db->isEntailed( q[1], subs, false, true ) ){
      Trace("inst-add-debug") << " --> Currently entailed." << std::endl;
      ++(d_statistics.d_inst_duplicate_ent);
      return false;
    }
    //Node eval = d_term_db->evaluateTerm( q[1], subs, false, true );
    //Trace("inst-add-debug2") << "Instantiation evaluates to : " << std::endl;
    //Trace("inst-add-debug2") << "   " << eval << std::endl;
  }

  //check for term vector duplication
  bool alreadyExists = !recordInstantiationInternal( q, terms, modEq );
  if( alreadyExists ){
    Trace("inst-add-debug") << " --> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate_eq);
    return false;
  }

  //construct the instantiation
  Trace("inst-add-debug") << "Constructing instantiation..." << std::endl;
  Assert( d_term_db->d_vars[q].size()==terms.size() );
  Node body = getInstantiation( q, d_term_db->d_vars[q], terms, doVts );  //do virtual term substitution
  Node orig_body = body;
  if( options::cbqiNestedQE() && d_i_cbqi ){
    body = d_i_cbqi->doNestedQE( q, terms, body, doVts );
  }  
  body = quantifiers::QuantifiersRewriter::preprocess( body, true );
  Trace("inst-debug") << "...preprocess to " << body << std::endl;

  //construct the lemma
  Trace("inst-assert") << "(assert " << body << ")" << std::endl;
  body = Rewriter::rewrite(body);
  Node lem;
  if( rlv_cond.empty() ){
    lem = NodeManager::currentNM()->mkNode( kind::OR, q.negate(), body );
  }else{
    rlv_cond.push_back( q.negate() );
    rlv_cond.push_back( body );
    lem = NodeManager::currentNM()->mkNode( kind::OR, rlv_cond );
  }
  lem = Rewriter::rewrite(lem);

  //check for lemma duplication
  if( addLemma( lem, true, false ) ){
    d_total_inst_debug[q]++;
    d_temp_inst_debug[q]++;
    d_total_inst_count_debug++;
    if( Trace.isOn("inst") ){
      Trace("inst") << "*** Instantiate " << q << " with " << std::endl;
      for( unsigned i=0; i<terms.size(); i++ ){
        if( Trace.isOn("inst") ){
          Trace("inst") << "   " << terms[i];
          if( Trace.isOn("inst-debug") ){
            Trace("inst-debug") << ", type=" << terms[i].getType() << ", var_type=" << q[0][i].getType();
          }
          Trace("inst") << std::endl;
        }
      }
    }
    if( options::instMaxLevel()!=-1 ){
      if( doVts ){
        //virtual term substitution/instantiation level features are incompatible
        Assert( false );
      }else{
        uint64_t maxInstLevel = 0;
        for( unsigned i=0; i<terms.size(); i++ ){
          if( terms[i].hasAttribute(InstLevelAttribute()) ){
            if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
              maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
            }
          }
        }
        setInstantiationLevelAttr( orig_body, q[1], maxInstLevel+1 );
      }
    }
    if( d_curr_effort_level>QEFFORT_CONFLICT && d_curr_effort_level<QEFFORT_NONE ){
      //notify listeners
      for( unsigned j=0; j<d_inst_notify.size(); j++ ){
        if( !d_inst_notify[j]->notifyInstantiation( d_curr_effort_level, q, lem, terms, body ) ){
          Trace("inst-add-debug") << "...we are in conflict." << std::endl;
          d_conflict = true;
          d_conflict_c = true;
          Assert( !d_lemmas_waiting.empty() );
          break;
        }
      }
    }
    if( options::trackInstLemmas() ){
      bool recorded;
      if( options::incrementalSolving() ){
        recorded = d_c_inst_match_trie[q]->recordInstLemma( q, terms, lem );
      }else{
        recorded = d_inst_match_trie[q].recordInstLemma( q, terms, lem );
      }
      Trace("inst-add-debug") << "...was recorded : " << recorded << std::endl;
      Assert( recorded );
    }
    Trace("inst-add-debug") << " --> Success." << std::endl;
    ++(d_statistics.d_instantiations);
    return true;
  }else{
    Trace("inst-add-debug") << " --> Lemma already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
}

bool QuantifiersEngine::removeInstantiation( Node q, Node lem, std::vector< Node >& terms ) {
  //lem must occur in d_waiting_lemmas
  if( removeLemma( lem ) ){
    return removeInstantiationInternal( q, terms );
  }else{
    return false;
  }
}

bool QuantifiersEngine::addSplit( Node n, bool reqPhase, bool reqPhasePol ){
  n = Rewriter::rewrite( n );
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  if( addLemma( lem ) ){
    Debug("inst") << "*** Add split " << n<< std::endl;
    return true;
  }
  return false;
}

bool QuantifiersEngine::addSplitEquality( Node n1, Node n2, bool reqPhase, bool reqPhasePol ){
  //Assert( !areEqual( n1, n2 ) );
  //Assert( !areDisequal( n1, n2 ) );
  Node fm = NodeManager::currentNM()->mkNode( EQUAL, n1, n2 );
  return addSplit( fm );
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
    if( !d_inst_notify.empty() ){
      unsigned prev_lem_sz = d_lemmas_waiting.size();
      for( unsigned j=0; j<d_inst_notify.size(); j++ ){
        d_inst_notify[j]->filterInstantiations();
      }  
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
  //only if unsat core available
  bool isUnsatCoreAvailable = false;
  if( options::proof() ){
    isUnsatCoreAvailable = ProofManager::currentPM()->unsatCoreAvailable();
  }
  if( isUnsatCoreAvailable ){
    Trace("inst-unsat-core") << "Get instantiations in unsat core..." << std::endl;
    ProofManager::currentPM()->getLemmasInUnsatCore(theory::THEORY_QUANTIFIERS, active_lemmas);
    if( Trace.isOn("inst-unsat-core") ){
      Trace("inst-unsat-core") << "Quantifiers lemmas in unsat core: " << std::endl;
      for (unsigned i = 0; i < active_lemmas.size(); ++i) {
        Trace("inst-unsat-core") << "  " << active_lemmas[i] << std::endl;
      }
      Trace("inst-unsat-core") << std::endl;
    }
    return true;
  }else{
    return false;
  }
}

bool QuantifiersEngine::getUnsatCoreLemmas( std::vector< Node >& active_lemmas, std::map< Node, Node >& weak_imp ) {
  if( getUnsatCoreLemmas( active_lemmas ) ){
    for (unsigned i = 0; i < active_lemmas.size(); ++i) {
      Node n = ProofManager::currentPM()->getWeakestImplicantInUnsatCore(active_lemmas[i]);
      if( n!=active_lemmas[i] ){
        Trace("inst-unsat-core") << "  weaken : " << active_lemmas[i] << " -> " << n << std::endl;
      }
      weak_imp[active_lemmas[i]] = n;
    }
    return true;
  }else{
    return false;
  }
}

void QuantifiersEngine::getInstantiationTermVectors( Node q, std::vector< std::vector< Node > >& tvecs ) {
  std::vector< Node > lemmas;
  getInstantiations( q, lemmas );
  std::map< Node, Node > quant;
  std::map< Node, std::vector< Node > > tvec;
  getExplanationForInstLemmas( lemmas, quant, tvec );
  for( std::map< Node, std::vector< Node > >::iterator it = tvec.begin(); it != tvec.end(); ++it ){
    tvecs.push_back( it->second );
  }
}

void QuantifiersEngine::getInstantiationTermVectors( std::map< Node, std::vector< std::vector< Node > > >& insts ) {
  if( options::incrementalSolving() ){
    for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
      getInstantiationTermVectors( it->first, insts[it->first] );
    }
  }else{
    for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
      getInstantiationTermVectors( it->first, insts[it->first] );
    }
  }
}

void QuantifiersEngine::getExplanationForInstLemmas( std::vector< Node >& lems, std::map< Node, Node >& quant, std::map< Node, std::vector< Node > >& tvec ) {
  if( options::trackInstLemmas() ){
    if( options::incrementalSolving() ){
      for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
        it->second->getExplanationForInstLemmas( it->first, lems, quant, tvec );
      }
    }else{
      for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
        it->second.getExplanationForInstLemmas( it->first, lems, quant, tvec );
      }
    }
#ifdef CVC4_ASSERTIONS
    for( unsigned j=0; j<lems.size(); j++ ){
      Assert( quant.find( lems[j] )!=quant.end() );
      Assert( tvec.find( lems[j] )!=tvec.end() );
    }
#endif
  }else{
    Assert( false );
  }
}

void QuantifiersEngine::printInstantiations( std::ostream& out ) {
  bool useUnsatCore = false;
  std::vector< Node > active_lemmas;
  if( options::trackInstLemmas() && getUnsatCoreLemmas( active_lemmas ) ){
    useUnsatCore = true;
  }

  bool printed = false;
  for( BoolMap::iterator it = d_skolemized.begin(); it != d_skolemized.end(); ++it ){
    Node q = (*it).first;
    printed = true;
    out << "(skolem " << q << std::endl;
    out << "  ( ";
    for( unsigned i=0; i<d_term_db->d_skolem_constants[q].size(); i++ ){
      if( i>0 ){ out << " "; }
      out << d_term_db->d_skolem_constants[q][i];
    }
    out << " )" << std::endl;
    out << ")" << std::endl;
  }
  if( options::incrementalSolving() ){
    for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
      bool firstTime = true;
      it->second->print( out, it->first, firstTime, useUnsatCore, active_lemmas );
      if( !firstTime ){
        out << ")" << std::endl;
      }      
      printed = printed || !firstTime;
    }
  }else{
    for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
      bool firstTime = true;
      it->second.print( out, it->first, firstTime, useUnsatCore, active_lemmas );
      if( !firstTime ){
        out << ")" << std::endl;
      }
      printed = printed || !firstTime;
    }
  }
  if( !printed ){
    out << "No instantiations" << std::endl;
  }
}

void QuantifiersEngine::printSynthSolution( std::ostream& out ) {
  if( d_ceg_inst ){
    d_ceg_inst->printSynthSolution( out );
  }else{
    out << "Internal error : module for synth solution not found." << std::endl;
  }
}

void QuantifiersEngine::getInstantiatedQuantifiedFormulas( std::vector< Node >& qs ) {
  if( options::incrementalSolving() ){
    for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
      qs.push_back( it->first );
    }
  }else{
    for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
      qs.push_back( it->first );
    }
  }
}

void QuantifiersEngine::getInstantiations( std::map< Node, std::vector< Node > >& insts ) {
  bool useUnsatCore = false;
  std::vector< Node > active_lemmas;
  if( options::trackInstLemmas() && getUnsatCoreLemmas( active_lemmas ) ){
    useUnsatCore = true;
  }

  if( options::incrementalSolving() ){
    for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
      it->second->getInstantiations( insts[it->first], it->first, this, useUnsatCore, active_lemmas );
    }
  }else{
    for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
      it->second.getInstantiations( insts[it->first], it->first, this, useUnsatCore, active_lemmas );
    }
  }
}

void QuantifiersEngine::getInstantiations( Node q, std::vector< Node >& insts  ) {
  if( options::incrementalSolving() ){
    std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.find( q );
    if( it!=d_c_inst_match_trie.end() ){
      std::vector< Node > active_lemmas;
      it->second->getInstantiations( insts, it->first, this, false, active_lemmas );
    }
  }else{
    std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.find( q );
    if( it!=d_inst_match_trie.end() ){
      std::vector< Node > active_lemmas;
      it->second.getInstantiations( insts, it->first, this, false, active_lemmas );
    }
  }
}

Node QuantifiersEngine::getInstantiatedConjunction( Node q ) {
  Assert( q.getKind()==FORALL );
  std::vector< Node > insts;
  getInstantiations( q, insts );
  if( insts.empty() ){
    return NodeManager::currentNM()->mkConst(true);
  }else{
    Node ret;
    if( insts.size()==1 ){
      ret = insts[0];
    }else{
      ret = NodeManager::currentNM()->mkNode( kind::AND, insts );
    }
    //have to remove q, TODO: avoid this in a better way
    TNode tq = q;
    TNode tt = d_term_db->d_true;
    ret = ret.substitute( tq, tt );
    return ret;
  }
}

QuantifiersEngine::Statistics::Statistics()
    : d_time("theory::QuantifiersEngine::time"),
      d_qcf_time("theory::QuantifiersEngine::time_qcf"),
      d_ematching_time("theory::QuantifiersEngine::time_ematching"),
      d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
      d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
      d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
      d_instantiations("QuantifiersEngine::Instantiations_Total", 0),
      d_inst_duplicate("QuantifiersEngine::Duplicate_Inst", 0),
      d_inst_duplicate_eq("QuantifiersEngine::Duplicate_Inst_Eq", 0),
      d_inst_duplicate_ent("QuantifiersEngine::Duplicate_Inst_Entailed", 0),
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
  smtStatisticsRegistry()->registerStat(&d_instantiations);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate_eq);
  smtStatisticsRegistry()->registerStat(&d_inst_duplicate_ent);
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
  smtStatisticsRegistry()->unregisterStat(&d_instantiations);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate_eq);
  smtStatisticsRegistry()->unregisterStat(&d_inst_duplicate_ent);
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
  return getTheoryEngine()->getMasterEqualityEngine();
}

void QuantifiersEngine::debugPrintEqualityEngine( const char * c ) {
  eq::EqualityEngine* ee = getMasterEqualityEngine();
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


EqualityQueryQuantifiersEngine::EqualityQueryQuantifiersEngine( context::Context* c, QuantifiersEngine* qe ) : d_qe( qe ), d_eqi_counter( c ), d_reset_count( 0 ){
  if( options::inferArithTriggerEq() ){
    d_eq_inference = new quantifiers::EqualityInference( c, options::inferArithTriggerEqExp() );
  }else{
    d_eq_inference = NULL;
  }
}

EqualityQueryQuantifiersEngine::~EqualityQueryQuantifiersEngine(){
  delete d_eq_inference;
}

bool EqualityQueryQuantifiersEngine::reset( Theory::Effort e ){
  d_int_rep.clear();
  d_reset_count++;
  return processInferences( e );
}

bool EqualityQueryQuantifiersEngine::processInferences( Theory::Effort e ) {
  if( options::inferArithTriggerEq() ){
    eq::EqualityEngine* ee = getEngine();
    //updated implementation
    while( d_eqi_counter.get()<d_eq_inference->getNumPendingMerges() ){
      Node eq = d_eq_inference->getPendingMerge( d_eqi_counter.get() );
      Node eq_exp = d_eq_inference->getPendingMergeExplanation( d_eqi_counter.get() );
      Trace("quant-engine-ee-proc") << "processInferences : Infer : " << eq << std::endl;
      Trace("quant-engine-ee-proc") << "      explanation : " << eq_exp << std::endl;
      Assert( ee->hasTerm( eq[0] ) );
      Assert( ee->hasTerm( eq[1] ) );
      if( areDisequal( eq[0], eq[1] ) ){
        Trace("quant-engine-ee-proc") << "processInferences : Conflict : " << eq << std::endl;
        if( Trace.isOn("term-db-lemma") ){
          Trace("term-db-lemma") << "Disequal terms, equal by normalization : " << eq[0] << " " << eq[1] << "!!!!" << std::endl;
          if( !d_qe->getTheoryEngine()->needCheck() ){
            Trace("term-db-lemma") << "  all theories passed with no lemmas." << std::endl;
            //this should really never happen (implies arithmetic is incomplete when sharing is enabled)
            Assert( false );
          }
          Trace("term-db-lemma") << "  add split on : " << eq << std::endl;
        }
        d_qe->addSplit( eq );
        return false;
      }else{
        ee->assertEquality( eq, true, eq_exp );
        d_eqi_counter = d_eqi_counter.get() + 1;
      }
    }
    Assert( ee->consistent() );
  }
  return true;
}

bool EqualityQueryQuantifiersEngine::hasTerm( Node a ){
  return getEngine()->hasTerm( a );
}

Node EqualityQueryQuantifiersEngine::getRepresentative( Node a ){
  eq::EqualityEngine* ee = getEngine();
  if( ee->hasTerm( a ) ){
    return ee->getRepresentative( a );
  }else{
    return a;
  }
}

bool EqualityQueryQuantifiersEngine::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      return ee->areEqual( a, b );
    }else{
      return false;
    }
  }
}

bool EqualityQueryQuantifiersEngine::areDisequal( Node a, Node b ){
  if( a==b ){
    return false;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      return ee->areDisequal( a, b, false );
    }else{
      return a.isConst() && b.isConst();
    }
  }
}

Node EqualityQueryQuantifiersEngine::getInternalRepresentative( Node a, Node f, int index ){
  Assert( f.isNull() || f.getKind()==FORALL );
  Node r = getRepresentative( a );
  if( options::finiteModelFind() ){
    if( r.isConst() && quantifiers::TermDb::containsUninterpretedConstant( r ) ){
      //map back from values assigned by model, if any
      if( d_qe->getModel() ){
        std::map< Node, Node >::iterator it = d_qe->getModel()->d_rep_set.d_values_to_terms.find( r );
        if( it!=d_qe->getModel()->d_rep_set.d_values_to_terms.end() ){
          r = it->second;
          r = getRepresentative( r );
        }else{
          if( r.getType().isSort() ){
            Trace("internal-rep-warn") << "No representative for UF constant." << std::endl;
            //should never happen : UF constants should never escape model
            Assert( false );
          }
        }
      }
    }
  }
  if( options::quantRepMode()==quantifiers::QUANT_REP_MODE_EE ){
    return r;
  }else{
    TypeNode v_tn = f.isNull() ? a.getType() : f[0][index].getType();
    std::map< Node, Node >::iterator itir = d_int_rep[v_tn].find( r );
    if( itir==d_int_rep[v_tn].end() ){
      //find best selection for representative
      Node r_best;
      //if( options::fmfRelevantDomain() && !f.isNull() ){
      //  Trace("internal-rep-debug") << "Consult relevant domain to mkRep " << r << std::endl;
      //  r_best = d_qe->getRelevantDomain()->getRelevantTerm( f, index, r );
      //  Trace("internal-rep-debug") << "Returned " << r_best << " " << r << std::endl;
      //}
      std::vector< Node > eqc;
      getEquivalenceClass( r, eqc );
      Trace("internal-rep-select") << "Choose representative for equivalence class : { ";
      for( unsigned i=0; i<eqc.size(); i++ ){
        if( i>0 ) Trace("internal-rep-select") << ", ";
        Trace("internal-rep-select") << eqc[i];
      }
      Trace("internal-rep-select")  << " }, type = " << v_tn << std::endl;
      int r_best_score = -1;
      for( size_t i=0; i<eqc.size(); i++ ){
        int score = getRepScore( eqc[i], f, index, v_tn );
        if( score!=-2 ){
          if( r_best.isNull() || ( score>=0 && ( r_best_score<0 || score<r_best_score ) ) ){
            r_best = eqc[i];
            r_best_score = score;
          }
        }
      }
      if( r_best.isNull() ){
        Trace("internal-rep-warn") << "No valid choice for representative in eqc class." << std::endl;
        r_best = r;
      }
      //now, make sure that no other member of the class is an instance
      std::hash_map<TNode, Node, TNodeHashFunction> cache;
      r_best = getInstance( r_best, eqc, cache );
      //store that this representative was chosen at this point
      if( d_rep_score.find( r_best )==d_rep_score.end() ){
        d_rep_score[ r_best ] = d_reset_count;
      }
      Trace("internal-rep-select") << "...Choose " << r_best << " with score " << r_best_score << std::endl;
      Assert( r_best.getType().isSubtypeOf( v_tn ) );
      d_int_rep[v_tn][r] = r_best;
      if( r_best!=a ){
        Trace("internal-rep-debug") << "rep( " << a << " ) = " << r << ", " << std::endl;
        Trace("internal-rep-debug") << "int_rep( " << a << " ) = " << r_best << ", " << std::endl;
      }
      return r_best;
    }else{
      return itir->second;
    }
  }
}

void EqualityQueryQuantifiersEngine::flattenRepresentatives( std::map< TypeNode, std::vector< Node > >& reps ) {
  //make sure internal representatives currently exist
  for( std::map< TypeNode, std::vector< Node > >::iterator it = reps.begin(); it != reps.end(); ++it ){
    if( it->first.isSort() ){
      for( unsigned i=0; i<it->second.size(); i++ ){
        Node r = getInternalRepresentative( it->second[i], Node::null(), 0 );
      }
    }
  }
  Trace("internal-rep-flatten") << "---Flattening representatives : " << std::endl;
  for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
    for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
      Trace("internal-rep-flatten") << itt->first << " : irep( " << it->first << " ) = " << it->second << std::endl;
    }
  }
  //store representatives for newly created terms
  std::map< Node, Node > temp_rep_map;

  bool success;
  do {
    success = false;
    for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
      for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
        if( it->second.getKind()==APPLY_UF && it->second.getType().isSort() ){
          Node ni = it->second;
          std::vector< Node > cc;
          cc.push_back( it->second.getOperator() );
          bool changed = false;
          for( unsigned j=0; j<ni.getNumChildren(); j++ ){
            if( ni[j].getType().isSort() ){
              Node r = getRepresentative( ni[j] );
              if( itt->second.find( r )==itt->second.end() ){
                Assert( temp_rep_map.find( r )!=temp_rep_map.end() );
                r = temp_rep_map[r];
              }
              if( r==ni ){
                //found sub-term as instance
                Trace("internal-rep-flatten-debug") << "...Changed " << it->second << " to subterm " << ni[j] << std::endl;
                itt->second[it->first] = ni[j];
                changed = false;
                success = true;
                break;
              }else{
                Node ir = itt->second[r];
                cc.push_back( ir );
                if( ni[j]!=ir ){
                  changed = true;
                }
              }
            }else{
              changed = false;
              break;
            }
          }
          if( changed ){
            Node n = NodeManager::currentNM()->mkNode( APPLY_UF, cc );
            Trace("internal-rep-flatten-debug") << "...Changed " << it->second << " to " << n << std::endl;
            success = true;
            itt->second[it->first] = n;
            temp_rep_map[n] = it->first;
          }
        }
      }
    }
  }while( success );
  Trace("internal-rep-flatten") << "---After flattening : " << std::endl;
  for( std::map< TypeNode, std::map< Node, Node > >::iterator itt = d_int_rep.begin(); itt != d_int_rep.end(); ++itt ){
    for( std::map< Node, Node >::iterator it = itt->second.begin(); it != itt->second.end(); ++it ){
      Trace("internal-rep-flatten") << itt->first << " : irep( " << it->first << " ) = " << it->second << std::endl;
    }
  }
}

eq::EqualityEngine* EqualityQueryQuantifiersEngine::getEngine(){
  return d_qe->getMasterEqualityEngine();
}

void EqualityQueryQuantifiersEngine::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  eq::EqualityEngine* ee = getEngine();
  if( ee->hasTerm( a ) ){
    Node rep = ee->getRepresentative( a );
    eq::EqClassIterator eqc_iter( rep, ee );
    while( !eqc_iter.isFinished() ){
      eqc.push_back( *eqc_iter );
      eqc_iter++;
    }
  }else{
    eqc.push_back( a );
  }
  //a should be in its equivalence class
  Assert( std::find( eqc.begin(), eqc.end(), a )!=eqc.end() );
}

TNode EqualityQueryQuantifiersEngine::getCongruentTerm( Node f, std::vector< TNode >& args ) {
  return d_qe->getTermDatabase()->getCongruentTerm( f, args );
}

//helper functions

Node EqualityQueryQuantifiersEngine::getInstance( Node n, const std::vector< Node >& eqc, std::hash_map<TNode, Node, TNodeHashFunction>& cache ){
  if(cache.find(n) != cache.end()) {
    return cache[n];
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = getInstance( n[i], eqc, cache );
    if( !nn.isNull() ){
      return cache[n] = nn;
    }
  }
  if( std::find( eqc.begin(), eqc.end(), n )!=eqc.end() ){
    return cache[n] = n;
  }else{
    return cache[n] = Node::null();
  }
}

//-2 : invalid, -1 : undesired, otherwise : smaller the score, the better
int EqualityQueryQuantifiersEngine::getRepScore( Node n, Node f, int index, TypeNode v_tn ){
  if( options::cbqi() && quantifiers::TermDb::hasInstConstAttr(n) ){  //reject
    return -2;
  }else if( !n.getType().isSubtypeOf( v_tn ) ){  //reject if incorrect type
    return -2;
  }else if( options::lteRestrictInstClosure() && ( !d_qe->getTermDatabase()->isInstClosure( n ) || !d_qe->getTermDatabase()->hasTermCurrent( n, false ) ) ){
    return -1;
  }else if( options::instMaxLevel()!=-1 ){
    //score prefer lowest instantiation level
    if( n.hasAttribute(InstLevelAttribute()) ){
      return n.getAttribute(InstLevelAttribute());
    }else{
      return options::instLevelInputOnly() ? -1 : 0;
    }
  }else{
    if( options::quantRepMode()==quantifiers::QUANT_REP_MODE_FIRST ){
      //score prefers earliest use of this term as a representative
      return d_rep_score.find( n )==d_rep_score.end() ? -1 : d_rep_score[n];
    }else{
      Assert( options::quantRepMode()==quantifiers::QUANT_REP_MODE_DEPTH );
      return quantifiers::TermDb::getTermDepth( n );
    }
  }
}

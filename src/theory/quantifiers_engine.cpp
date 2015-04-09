/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of quantifiers engine class
 **/

#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/equality_engine.h"
#include "theory/arrays/theory_arrays.h"
#include "theory/datatypes/theory_datatypes.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/options.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/quantifiers/quant_conflict_find.h"
#include "theory/quantifiers/conjecture_generator.h"
#include "theory/quantifiers/ce_guided_instantiation.h"
#include "theory/quantifiers/local_theory_ext.h"
#include "theory/quantifiers/relevant_domain.h"
#include "theory/uf/options.h"
#include "theory/uf/theory_uf.h"
#include "theory/quantifiers/full_model_check.h"
#include "theory/quantifiers/ambqi_builder.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;


eq::EqualityEngine * QuantifiersModule::getEqualityEngine() {
  return d_quantEngine->getMasterEqualityEngine();
}

bool QuantifiersModule::areEqual( TNode n1, TNode n2 ) {
  eq::EqualityEngine * ee = getEqualityEngine();
  return n1==n2 || ( ee->hasTerm( n1 ) && ee->hasTerm( n2 ) && ee->areEqual( n1, n2 ) );
}

bool QuantifiersModule::areDisequal( TNode n1, TNode n2 ) {
  eq::EqualityEngine * ee = getEqualityEngine();
  return n1!=n2 && ee->hasTerm( n1 ) && ee->hasTerm( n2 ) && ee->areDisequal( n1, n2, false );
}

TNode QuantifiersModule::getRepresentative( TNode n ) {
  eq::EqualityEngine * ee = getEqualityEngine();
  if( ee->hasTerm( n ) ){
    return ee->getRepresentative( n );
  }else{
    return n;
  }
}

quantifiers::TermDb * QuantifiersModule::getTermDatabase() {
  return d_quantEngine->getTermDatabase();
}

QuantifiersEngine::QuantifiersEngine(context::Context* c, context::UserContext* u, TheoryEngine* te):
d_te( te ),
d_lemmas_produced_c(u){
  d_eq_query = new EqualityQueryQuantifiersEngine( this );
  d_term_db = new quantifiers::TermDb( c, u, this );
  d_tr_trie = new inst::TriggerTrie;
  //d_rr_tr_trie = new rrinst::TriggerTrie;
  //d_eem = new EfficientEMatcher( this );
  d_hasAddedLemma = false;

  bool needsBuilder = false;

  Trace("quant-engine-debug") << "Initialize model, mbqi : " << options::mbqiMode() << std::endl;

  //the model object
  if( options::mbqiMode()==quantifiers::MBQI_FMC ||
      options::mbqiMode()==quantifiers::MBQI_FMC_INTERVAL || options::fmfBoundInt() ||
      options::mbqiMode()==quantifiers::MBQI_TRUST ){
    d_model = new quantifiers::fmcheck::FirstOrderModelFmc( this, c, "FirstOrderModelFmc" );
  }else if( options::mbqiMode()==quantifiers::MBQI_ABS ){
    d_model = new quantifiers::FirstOrderModelAbs( this, c, "FirstOrderModelAbs" );
  }else{
    d_model = new quantifiers::FirstOrderModelIG( this, c, "FirstOrderModelIG" );
  }
  if( !options::finiteModelFind() ){
    d_rel_dom = new quantifiers::RelevantDomain( this, d_model );
  }else{
    d_rel_dom = NULL;
  }
  if( options::relevantTriggers() ){
    d_quant_rel = new QuantRelevance( false );
  }else{
    d_quant_rel = NULL;
  }

  //add quantifiers modules
  if( options::quantConflictFind() || options::quantRewriteRules() ){
    d_qcf = new quantifiers::QuantConflictFind( this, c);
    d_modules.push_back( d_qcf );
  }else{
    d_qcf = NULL;
  }
  if( options::conjectureGen() ){
    d_sg_gen = new quantifiers::ConjectureGenerator( this, c );
    d_modules.push_back( d_sg_gen );
  }else{
    d_sg_gen = NULL;
  }
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    //the instantiation must set incomplete flag unless finite model finding is turned on
    d_inst_engine = new quantifiers::InstantiationEngine( this, !options::finiteModelFind() );
    d_modules.push_back(  d_inst_engine );
  }else{
    d_inst_engine = NULL;
  }
  if( options::finiteModelFind()  ){
    if( options::fmfBoundInt() ){
      d_bint = new quantifiers::BoundedIntegers( c, this );
      d_modules.push_back( d_bint );
    }else{
      d_bint = NULL;
    }
    d_model_engine = new quantifiers::ModelEngine( c, this );
    d_modules.push_back( d_model_engine );
    needsBuilder = true;
  }else{
    d_model_engine = NULL;
    d_bint = NULL;
  }
  if( options::quantRewriteRules() ){
    d_rr_engine = new quantifiers::RewriteEngine( c, this );
    d_modules.push_back(d_rr_engine);
  }else{
    d_rr_engine = NULL;
  }
  if( options::ceGuidedInst() ){
    d_ceg_inst = new quantifiers::CegInstantiation( this, c );
    d_modules.push_back( d_ceg_inst );
    needsBuilder = true;
  }else{
    d_ceg_inst = NULL;
  }
  if( options::ltePartialInst() ){
    d_lte_part_inst = new quantifiers::LtePartialInst( this, c );
    d_modules.push_back( d_lte_part_inst );
  }else{
    d_lte_part_inst = NULL;
  }

  if( needsBuilder ){
    Trace("quant-engine-debug") << "Initialize model engine, mbqi : " << options::mbqiMode() << " " << options::fmfBoundInt() << std::endl;
    if( options::mbqiMode()==quantifiers::MBQI_FMC || options::mbqiMode()==quantifiers::MBQI_FMC_INTERVAL ||
        options::mbqiMode()==quantifiers::MBQI_TRUST || options::fmfBoundInt() ){
      Trace("quant-engine-debug") << "...make fmc builder." << std::endl;
      d_builder = new quantifiers::fmcheck::FullModelChecker( c, this );
    }else if( options::mbqiMode()==quantifiers::MBQI_ABS ){
      Trace("quant-engine-debug") << "...make abs mbqi builder." << std::endl;
      d_builder = new quantifiers::AbsMbqiBuilder( c, this );
    }else{
      Trace("quant-engine-debug") << "...make default model builder." << std::endl;
      d_builder = new quantifiers::QModelBuilderDefault( c, this );
    }
  }else{
    d_builder = NULL;
  }

  d_total_inst_count_debug = 0;
  d_ierCounter = 0;
  d_ierCounter_lc = 0;
}

QuantifiersEngine::~QuantifiersEngine(){
  delete d_builder;
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
  for(std::map< Node, QuantPhaseReq* >::iterator i = d_phase_reqs.begin(); i != d_phase_reqs.end(); ++i) {
    delete (*i).second;
  }
}

EqualityQueryQuantifiersEngine* QuantifiersEngine::getEqualityQuery() {
  return d_eq_query;
}

context::Context* QuantifiersEngine::getSatContext(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getSatContext();
}

context::Context* QuantifiersEngine::getUserContext(){
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
  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->finishInit();
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

void QuantifiersEngine::setOwner( Node q, QuantifiersModule * m ) {
  QuantifiersModule * mo = getOwner( q );
  if( mo!=m ){
    if( mo!=NULL ){
      Trace("quant-warn") << "WARNING: setting owner of " << q << " to " << ( m ? m->identify() : "null" ) << ", but already has owner " << mo->identify() << "!" << std::endl;
    }
    d_owner[q] = m;
  }
}

bool QuantifiersEngine::hasOwnership( Node q, QuantifiersModule * m ) {
  QuantifiersModule * mo = getOwner( q );
  return mo==m || mo==NULL;
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_time);
  if( !getMasterEqualityEngine()->consistent() ){
    Trace("quant-engine-debug") << "Master equality engine not consistent, return." << std::endl;
    return;
  }
  if( e==Theory::EFFORT_FULL ){
    d_ierCounter++;
  }else if( e==Theory::EFFORT_LAST_CALL ){
    d_ierCounter_lc++;
  }
  bool needsCheck = !d_lemmas_waiting.empty();
  bool needsModel = false;
  bool needsFullModel = false;
  std::vector< QuantifiersModule* > qm;
  if( d_model->checkNeeded() ){
    needsCheck = needsCheck || e>=Theory::EFFORT_LAST_CALL;  //always need to check at or above last call
    for( int i=0; i<(int)d_modules.size(); i++ ){
      if( d_modules[i]->needsCheck( e ) ){
        qm.push_back( d_modules[i] );
        needsCheck = true;
        if( d_modules[i]->needsModel( e ) ){
          needsModel = true;
          if( d_modules[i]->needsFullModel( e ) ){
            needsFullModel = true;
          }
        }
      }
    }
  }
  if( needsCheck ){
    Trace("quant-engine") << "Quantifiers Engine check, level = " << e << std::endl;
    if( Trace.isOn("quant-engine-debug") ){
      Trace("quant-engine-debug") << "  modules to check : ";
      for( unsigned i=0; i<qm.size(); i++ ){
        Trace("quant-engine-debug") << qm[i]->identify() << " ";
      }
      Trace("quant-engine-debug") << std::endl;
      Trace("quant-engine-debug") << "  # quantified formulas = " << d_model->getNumAssertedQuantifiers() << std::endl;
      if( d_model->getNumToReduceQuantifiers()>0 ){
        Trace("quant-engine-debug") << "  # quantified formulas to reduce = " << d_model->getNumToReduceQuantifiers() << std::endl;
      }
      if( !d_lemmas_waiting.empty() ){
        Trace("quant-engine-debug") << "  lemmas waiting = " << d_lemmas_waiting.size() << std::endl;
      }
      Trace("quant-engine-debug") << "  Theory engine finished : " << !d_te->needCheck() << std::endl;
      Trace("quant-engine-debug") << "Resetting all modules..." << std::endl;
    }
    if( Trace.isOn("quant-engine-ee") ){
      Trace("quant-engine-ee") << "Equality engine : " << std::endl;
      debugPrintEqualityEngine( "quant-engine-ee" );
    }

    //reset relevant information
    d_conflict = false;
    d_hasAddedLemma = false;

    //flush previous lemmas (for instance, if was interupted), or other lemmas to process
    flushLemmas();
    if( d_hasAddedLemma ){
      return;
    }

    Trace("quant-engine-debug2") << "Reset term db..." << std::endl;
    d_term_db->reset( e );
    d_eq_query->reset();
    if( d_rel_dom ){
      d_rel_dom->reset();
    }
    d_model->reset_round();
    for( unsigned i=0; i<d_modules.size(); i++ ){
      Trace("quant-engine-debug2") << "Reset " << d_modules[i]->identify().c_str() << std::endl;
      d_modules[i]->reset_round( e );
    }
    Trace("quant-engine-debug") << "Done resetting all modules." << std::endl;

    if( e==Theory::EFFORT_LAST_CALL ){
      //if effort is last call, try to minimize model first FIXME: remove?
      uf::StrongSolverTheoryUF * ufss = ((uf::TheoryUF*)getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver();
      if( ufss && !ufss->minimize() ){
        return;
      }
      ++(d_statistics.d_instantiation_rounds_lc);
    }else if( e==Theory::EFFORT_FULL ){
      ++(d_statistics.d_instantiation_rounds);
    }

    Trace("quant-engine-debug") << "Check modules that needed check..." << std::endl;
    for( unsigned quant_e = QEFFORT_CONFLICT; quant_e<=QEFFORT_MODEL; quant_e++ ){
      bool success = true;
      //build the model if any module requested it
      if( quant_e==QEFFORT_MODEL && needsModel ){
        Assert( d_builder!=NULL );
        Trace("quant-engine-debug") << "Build model, fullModel = " << ( needsFullModel || d_builder->optBuildAtFullModel() ) << "..." << std::endl;
        d_builder->d_addedLemmas = 0;
        d_builder->buildModel( d_model, needsFullModel || d_builder->optBuildAtFullModel() );
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
        }
      }
      //flush all current lemmas
      flushLemmas();
      //if we have added one, stop
      if( d_hasAddedLemma ){
        break;
      //otherwise, complete the model generation if necessary
      }else if( quant_e==QEFFORT_MODEL && needsModel && options::produceModels() && !needsFullModel && !d_builder->optBuildAtFullModel() ){
        Trace("quant-engine-debug") << "Build completed model..." << std::endl;
        d_builder->buildModel( d_model, true );
      }
    }
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
    Trace("quant-engine") << "Finished quantifiers engine check." << std::endl;
  }
  //SAT case
  if( e==Theory::EFFORT_LAST_CALL && !d_hasAddedLemma ){
    if( options::produceModels() && !d_model->isModelSet() ){
      //use default model builder when no module built the model
      Trace("quant-engine-debug") << "Build the model..." << std::endl;
      d_te->getModelBuilder()->buildModel( d_model, true );
      Trace("quant-engine-debug") << "Done building the model." << std::endl;
    }
    //check other sources of incompleteness
    bool setInc = false;
    if( d_lte_part_inst && d_lte_part_inst->wasInvoked() ){
      setInc = true;
    }
    if( setInc ){
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

bool QuantifiersEngine::registerQuantifier( Node f ){
  std::map< Node, bool >::iterator it = d_quants.find( f );
  if( it==d_quants.end() ){
    Trace("quant") << "QuantifiersEngine : Register quantifier ";
    Trace("quant") << " : " << f << std::endl;
    ++(d_statistics.d_num_quant);
    Assert( f.getKind()==FORALL );

    //check whether we should apply a reduction
    bool reduced = false;
    if( d_lte_part_inst && !f.getAttribute(LtePartialInstAttribute()) ){
      Trace("lte-partial-inst") << "LTE: Partially instantiate " << f << "?" << std::endl;
      if( d_lte_part_inst->addQuantifier( f ) ){
        reduced = true;
      }
    }
    if( reduced ){
      d_model->assertQuantifier( f, true );
      d_quants[f] = false;
      return false;
    }else{
      //make instantiation constants for f
      d_term_db->makeInstantiationConstantsFor( f );
      d_term_db->computeAttributes( f );
      QuantifiersModule * qm = getOwner( f );
      if( qm!=NULL ){
        Trace("quant") << "   Owner : " << qm->identify() << std::endl;
      }
      //register with quantifier relevance
      if( d_quant_rel ){
        d_quant_rel->registerQuantifier( f );
      }
      //register with each module
      for( int i=0; i<(int)d_modules.size(); i++ ){
        d_modules[i]->registerQuantifier( f );
      }
      Node ceBody = d_term_db->getInstConstantBody( f );
      //generate the phase requirements
      d_phase_reqs[f] = new QuantPhaseReq( ceBody, true );
      //also register it with the strong solver
      if( options::finiteModelFind() ){
        ((uf::TheoryUF*)d_te->theoryOf( THEORY_UF ))->getStrongSolver()->registerQuantifier( f );
      }
      d_quants[f] = true;
      return true;
    }
  }else{
    return it->second;
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
    //do skolemization
    if( d_skolemized.find( f )==d_skolemized.end() ){
      Node body = d_term_db->getSkolemizedBody( f );
      NodeBuilder<> nb(kind::OR);
      nb << f << body.notNode();
      Node lem = nb;
      if( Trace.isOn("quantifiers-sk") ){
        Node slem = Rewriter::rewrite( lem );
        Trace("quantifiers-sk") << "Skolemize lemma : " << slem << std::endl;
      }
      getOutputChannel().lemma( lem, false, true );
      d_skolemized[f] = true;
    }
  }
  //assert to modules TODO : handle !pol
  if( pol ){
    //register the quantifier
    bool nreduced = registerQuantifier( f );
    //assert it to each module
    if( nreduced ){
      d_model->assertQuantifier( f );
      for( int i=0; i<(int)d_modules.size(); i++ ){
        d_modules[i]->assertNode( f );
      }
    }
  }
}

void QuantifiersEngine::propagate( Theory::Effort level ){
  CodeTimer codeTimer(d_time);

  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->propagate( level );
  }
}

Node QuantifiersEngine::getNextDecisionRequest(){
  for( int i=0; i<(int)d_modules.size(); i++ ){
    Node n = d_modules[i]->getNextDecisionRequest();
    if( !n.isNull() ){
      return n;
    }
  }
  return Node::null();
}

quantifiers::TermDbSygus* QuantifiersEngine::getTermDatabaseSygus() {
  return getTermDatabase()->getTermDatabaseSygus();
}

void QuantifiersEngine::addTermToDatabase( Node n, bool withinQuant, bool withinInstClosure ){
  std::set< Node > added;
  getTermDatabase()->addTerm( n, added, withinQuant, withinInstClosure );
  //maybe have triggered instantiations if we are doing eager instantiation
  if( options::eagerInstQuant() ){
    flushLemmas();
  }
  //added contains also the Node that just have been asserted in this branch
  if( d_quant_rel ){
    for( std::set< Node >::iterator i=added.begin(), end=added.end(); i!=end; i++ ){
      if( !withinQuant ){
        d_quant_rel->setRelevance( i->getOperator(), 0 );
      }
    }
  }
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

bool QuantifiersEngine::addInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms ){
  Assert( f.getKind()==FORALL );
  Assert( vars.size()==terms.size() );
  Node body = getInstantiation( f, vars, terms );
  Trace("inst-assert") << "(assert " << body << ")" << std::endl;
  //make the lemma
  NodeBuilder<> nb(kind::OR);
  nb << f.notNode() << body;
  Node lem = nb;
  //check for duplication
  if( addLemma( lem ) ){
    d_total_inst_debug[f]++;
    d_temp_inst_debug[f]++;
    d_total_inst_count_debug++;
    Trace("inst") << "*** Instantiate " << f << " with " << std::endl;
    for( int i=0; i<(int)terms.size(); i++ ){
      Trace("inst") << "   " << terms[i];
      Trace("inst") << std::endl;
      Assert( terms[i].getType().isSubtypeOf( f[0][i].getType() ) );
    }
    if( options::cbqi() && !options::cbqi2() ){
      for( int i=0; i<(int)terms.size(); i++ ){
        if( quantifiers::TermDb::hasInstConstAttr(terms[i]) ){
          Debug("inst")<< "***& Bad Instantiate " << f << " with " << std::endl;
          for( int i=0; i<(int)terms.size(); i++ ){
            Debug("inst") << "   " << terms[i] << std::endl;
          }
          Unreachable("Bad instantiation");
        }
      }
    }
    if( options::instMaxLevel()!=-1 ){
      uint64_t maxInstLevel = 0;
      for( int i=0; i<(int)terms.size(); i++ ){
        if( terms[i].hasAttribute(InstLevelAttribute()) ){
          if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
            maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
          }
        }
      }
      setInstantiationLevelAttr( body, f[1], maxInstLevel+1 );
    }
    ++(d_statistics.d_instantiations);
    return true;
  }else{
    ++(d_statistics.d_inst_duplicate);
    return false;
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
    }
    Assert( n.getNumChildren()==qn.getNumChildren() );
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      setInstantiationLevelAttr( n[i], qn[i], level );
    }
  }
}

void QuantifiersEngine::setInstantiationLevelAttr( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
    Trace("inst-level-debug") << "Set instantiation level " << n << " to " << level << std::endl;
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevelAttr( n[i], level );
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


Node QuantifiersEngine::getInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms ){
  Node body;
  //process partial instantiation if necessary
  if( d_term_db->d_vars[f].size()!=vars.size() ){
    body = f[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
    std::vector< Node > uninst_vars;
    //doing a partial instantiation, must add quantifier for all uninstantiated variables
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      if( std::find( vars.begin(), vars.end(), f[0][i] )==vars.end() ){
        uninst_vars.push_back( f[0][i] );
      }
    }
    Node bvl = NodeManager::currentNM()->mkNode( BOUND_VAR_LIST, uninst_vars );
    body = NodeManager::currentNM()->mkNode( FORALL, bvl, body );
    Trace("partial-inst") << "Partial instantiation : " << f << std::endl;
    Trace("partial-inst") << "                      : " << body << std::endl;
  }else{
    if( options::cbqi() ){
      body = f[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
    }else{
      //do optimized version
      Node icb = d_term_db->getInstConstantBody( f );
      body = getSubstitute( icb, terms );
      if( Debug.isOn("check-inst") ){
        Node body2 = f[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
        if( body!=body2 ){
          Debug("check-inst") << "Substitution is wrong : " << body << " " << body2 << std::endl;
        }
      }
    }
  }
  return body;
}

Node QuantifiersEngine::getInstantiation( Node f, InstMatch& m ){
  std::vector< Node > vars;
  std::vector< Node > terms;
  computeTermVector( f, m, vars, terms );
  return getInstantiation( f, vars, terms );
}

Node QuantifiersEngine::getInstantiation( Node f, std::vector< Node >& terms ) {
  return getInstantiation( f, d_term_db->d_inst_constants[f], terms );
}

/*
bool QuantifiersEngine::existsInstantiation( Node f, InstMatch& m, bool modEq, bool modInst ){
  if( options::incrementalSolving() ){
    if( d_c_inst_match_trie.find( f )!=d_c_inst_match_trie.end() ){
      if( d_c_inst_match_trie[f]->existsInstMatch( this, f, m, getUserContext(), modEq, modInst ) ){
        return true;
      }
    }
  }else{
    if( d_inst_match_trie.find( f )!=d_inst_match_trie.end() ){
      if( d_inst_match_trie[f].existsInstMatch( this, f, m, modEq, modInst ) ){
        return true;
      }
    }
  }
  //also check model builder (it may contain instantiations internally)
  if( d_builder && d_builder->existsInstantiation( f, m, modEq, modInst ) ){
    return true;
  }
  return false;
}
*/

bool QuantifiersEngine::addLemma( Node lem, bool doCache ){
  if( doCache ){
    lem = Rewriter::rewrite(lem);
    Trace("inst-add-debug2") << "Adding lemma : " << lem << std::endl;
    if( d_lemmas_produced_c.find( lem )==d_lemmas_produced_c.end() ){
      //d_curr_out->lemma( lem, false, true );
      d_lemmas_produced_c[ lem ] = true;
      d_lemmas_waiting.push_back( lem );
      Trace("inst-add-debug2") << "Added lemma : " << lem << std::endl;
      return true;
    }else{
      Trace("inst-add-debug2") << "Duplicate." << std::endl;
      return false;
    }
  }else{
    d_lemmas_waiting.push_back( lem );
    return true;
  }
}

void QuantifiersEngine::addRequirePhase( Node lit, bool req ){
  d_phase_req_waiting[lit] = req;
}

bool QuantifiersEngine::addInstantiation( Node f, InstMatch& m, bool mkRep, bool modEq, bool modInst ){
  // For resource-limiting (also does a time check).
  getOutputChannel().safePoint();

  std::vector< Node > terms;
  //make sure there are values for each variable we are instantiating
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node val = m.get( i );
    if( val.isNull() ){
      Node ic = d_term_db->getInstantiationConstant( f, i );
      val = d_term_db->getFreeVariableForInstConstant( ic );
      Trace("inst-add-debug") << "mkComplete " << val << std::endl;
    }
    terms.push_back( val );
  }
  return addInstantiation( f, terms, mkRep, modEq, modInst );
}

bool QuantifiersEngine::addInstantiation( Node f, std::vector< Node >& terms, bool mkRep, bool modEq, bool modInst ) {
  Assert( terms.size()==f[0].getNumChildren() );
  Trace("inst-add-debug") << "Add instantiation: ";
  for( unsigned i=0; i<terms.size(); i++ ){
    if( i>0 ) Trace("inst-add-debug") << ", ";
    Trace("inst-add-debug") << f[0][i] << " -> " << terms[i];
    //make it representative, this is helpful for recognizing duplication
    if( mkRep ){
      //pick the best possible representative for instantiation, based on past use and simplicity of term
      terms[i] = d_eq_query->getInternalRepresentative( terms[i], f, i );
      Trace("inst-add-debug2") << " (" << terms[i] << ")";
    }
  }
  Trace("inst-add-debug") << std::endl;

  //check based on instantiation level
  if( options::instMaxLevel()!=-1 || options::lteRestrictInstClosure() ){
    for( unsigned i=0; i<terms.size(); i++ ){
      if( !d_term_db->isTermEligibleForInstantiation( terms[i], f, true ) ){
        return false;
      }
    }
  }
  //check for entailment
  if( options::instNoEntail() ){
    std::map< TNode, TNode > subs;
    for( unsigned i=0; i<terms.size(); i++ ){
      subs[f[0][i]] = terms[i];
    }
    if( d_term_db->isEntailed( f[1], subs, false, true ) ){
      Trace("inst-add-debug") << " -> Currently entailed." << std::endl;
      return false;
    }
  }

  //check for duplication
  bool alreadyExists = false;
  if( options::incrementalSolving() ){
    Trace("inst-add-debug") << "Adding into context-dependent inst trie, modEq = " << modEq << ", modInst = " << modInst << std::endl;
    inst::CDInstMatchTrie* imt;
    std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.find( f );
    if( it!=d_c_inst_match_trie.end() ){
      imt = it->second;
    }else{
      imt = new CDInstMatchTrie( getUserContext() );
      d_c_inst_match_trie[f] = imt;
    }
    alreadyExists = !imt->addInstMatch( this, f, terms, getUserContext(), modEq, modInst );
  }else{
    Trace("inst-add-debug") << "Adding into inst trie" << std::endl;
    alreadyExists = !d_inst_match_trie[f].addInstMatch( this, f, terms, modEq, modInst );
  }
  if( alreadyExists ){
    Trace("inst-add-debug") << " -> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate_eq);
    return false;
  }


  //add the instantiation
  Trace("inst-add-debug") << "Constructing instantiation..." << std::endl;
  bool addedInst = addInstantiation( f, d_term_db->d_vars[f], terms );
  //report the result
  if( addedInst ){
    Trace("inst-add-debug") << " -> Success." << std::endl;
    return true;
  }else{
    Trace("inst-add-debug") << " -> Lemma already exists." << std::endl;
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
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  return addSplit( fm );
}

bool QuantifiersEngine::getInstWhenNeedsCheck( Theory::Effort e ) {
  //determine if we should perform check, based on instWhenMode
  bool performCheck = false;
  if( options::instWhenMode()==quantifiers::INST_WHEN_FULL ){
    performCheck = ( e >= Theory::EFFORT_FULL );
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_FULL_DELAY ){
    performCheck = ( e >= Theory::EFFORT_FULL ) && !getTheoryEngine()->needCheck();
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_FULL_LAST_CALL ){
    performCheck = ( ( e==Theory::EFFORT_FULL  && d_ierCounter%2==0 ) || e==Theory::EFFORT_LAST_CALL );
  }else if( options::instWhenMode()==quantifiers::INST_WHEN_LAST_CALL ){
    performCheck = ( e >= Theory::EFFORT_LAST_CALL );
  }else{
    performCheck = true;
  }
  if( e==Theory::EFFORT_LAST_CALL ){
    //with bounded integers, skip every other last call,
    // since matching loops may occur with infinite quantification
    if( d_ierCounter_lc%2==0 && options::fmfBoundInt() ){
      performCheck = false;
    }
  }
  return performCheck;
}

void QuantifiersEngine::flushLemmas(){
  if( !d_lemmas_waiting.empty() ){
    //take default output channel if none is provided
    d_hasAddedLemma = true;
    for( int i=0; i<(int)d_lemmas_waiting.size(); i++ ){
      getOutputChannel().lemma( d_lemmas_waiting[i], false, true );
    }
    d_lemmas_waiting.clear();
  }
  if( !d_phase_req_waiting.empty() ){
    for( std::map< Node, bool >::iterator it = d_phase_req_waiting.begin(); it != d_phase_req_waiting.end(); ++it ){
      getOutputChannel().requirePhase( it->first, it->second );
    }
    d_phase_req_waiting.clear();
  }
}

void QuantifiersEngine::getPhaseReqTerms( Node f, std::vector< Node >& nodes ){
  if( options::literalMatchMode()!=quantifiers::LITERAL_MATCH_NONE && d_phase_reqs.find( f )!=d_phase_reqs.end() ){
    // doing literal-based matching (consider polarity of literals)
    for( int i=0; i<(int)nodes.size(); i++ ){
      Node prev = nodes[i];
      if( d_phase_reqs[f]->isPhaseReq( nodes[i] ) ){
        bool preq = d_phase_reqs[f]->getPhaseReq( nodes[i] );
        nodes[i] = NodeManager::currentNM()->mkNode( IFF, nodes[i], NodeManager::currentNM()->mkConst<bool>(preq) );
      }
      //else if( qe->isPhaseReqEquality( f, trNodes[i] ) ){
      //  Node req = qe->getPhaseReqEquality( f, trNodes[i] );
      //  trNodes[i] = NodeManager::currentNM()->mkNode( EQUAL, trNodes[i], req );
      //}
    }
  }
}

void QuantifiersEngine::printInstantiations( std::ostream& out ) {
  for( std::map< Node, bool >::iterator it = d_skolemized.begin(); it != d_skolemized.end(); ++it ){
    out << "Skolem constants of " << it->first << " : " << std::endl;
    out << "  ( ";
    for( unsigned i=0; i<d_term_db->d_skolem_constants[it->first].size(); i++ ){
      if( i>0 ){ out << ", "; }
      out << d_term_db->d_skolem_constants[it->first][i];
    }
    out << " )" << std::endl;
    out << std::endl;
  }
  if( options::incrementalSolving() ){
    for( std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_c_inst_match_trie.begin(); it != d_c_inst_match_trie.end(); ++it ){
      out << "Instantiations of " << it->first << " : " << std::endl;
      it->second->print( out, it->first );
    }
  }else{
    for( std::map< Node, inst::InstMatchTrie >::iterator it = d_inst_match_trie.begin(); it != d_inst_match_trie.end(); ++it ){
      out << "Instantiations of " << it->first << " : " << std::endl;
      it->second.print( out, it->first );
      out << std::endl;
    }
  }
}

void QuantifiersEngine::printSynthSolution( std::ostream& out ) {
  if( d_ceg_inst ){
    d_ceg_inst->printSynthSolution( out );
  }else{
    out << "Internal error : module for synth solution not found." << std::endl;
  }
}

QuantifiersEngine::Statistics::Statistics():
  d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
  d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
  d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
  d_instantiations("QuantifiersEngine::Instantiations_Total", 0),
  d_inst_duplicate("QuantifiersEngine::Duplicate_Inst", 0),
  d_inst_duplicate_eq("QuantifiersEngine::Duplicate_Inst_Eq", 0),
  d_triggers("QuantifiersEngine::Triggers", 0),
  d_simple_triggers("QuantifiersEngine::Triggers_Simple", 0),
  d_multi_triggers("QuantifiersEngine::Triggers_Multi", 0),
  d_multi_trigger_instantiations("QuantifiersEngine::Multi_Trigger_Instantiations", 0)
{
  StatisticsRegistry::registerStat(&d_num_quant);
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
  StatisticsRegistry::registerStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_inst_duplicate);
  StatisticsRegistry::registerStat(&d_inst_duplicate_eq);
  StatisticsRegistry::registerStat(&d_triggers);
  StatisticsRegistry::registerStat(&d_simple_triggers);
  StatisticsRegistry::registerStat(&d_multi_triggers);
  StatisticsRegistry::registerStat(&d_multi_trigger_instantiations);
}

QuantifiersEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_num_quant);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate_eq);
  StatisticsRegistry::unregisterStat(&d_triggers);
  StatisticsRegistry::unregisterStat(&d_simple_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_trigger_instantiations);
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

void EqualityQueryQuantifiersEngine::reset(){
  d_int_rep.clear();
  d_reset_count++;
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
    if( d_liberal ){
      return true;//!areDisequal( a, b );
    }else{
      if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
        if( ee->areEqual( a, b ) ){
          return true;
        }
      }
      return false;
    }
  }
}

bool EqualityQueryQuantifiersEngine::areDisequal( Node a, Node b ){
  eq::EqualityEngine* ee = getEngine();
  if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
    if( ee->areDisequal( a, b, false ) ){
      return true;
    }
  }
  return false;
}

Node EqualityQueryQuantifiersEngine::getInternalRepresentative( Node a, Node f, int index ){
  Node r = getRepresentative( a );
  if( !options::internalReps() ){
    return r;
  }else{
    if( d_int_rep.find( r )==d_int_rep.end() ){
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
      Trace("internal-rep-select")  << " } " << std::endl;
      int r_best_score = -1;
      for( size_t i=0; i<eqc.size(); i++ ){
        //if cbqi is active, do not choose instantiation constant terms
        if( !options::cbqi() || !quantifiers::TermDb::hasInstConstAttr(eqc[i]) ){
          int score = getRepScore( eqc[i], f, index );
          if( r_best.isNull() || ( score>=0 && ( r_best_score<0 || score<r_best_score ) ) ){
            r_best = eqc[i];
            r_best_score = score;
          }
        }
      }
      if( r_best.isNull() ){
        if( !f.isNull() ){
          Node ic = d_qe->getTermDatabase()->getInstantiationConstant( f, index );
          r_best = d_qe->getTermDatabase()->getFreeVariableForInstConstant( ic );
        }else{
          r_best = a;
        }
      }
      //now, make sure that no other member of the class is an instance
      std::hash_map<TNode, Node, TNodeHashFunction> cache;
      r_best = getInstance( r_best, eqc, cache );
      //store that this representative was chosen at this point
      if( d_rep_score.find( r_best )==d_rep_score.end() ){
        d_rep_score[ r_best ] = d_reset_count;
      }
      Trace("internal-rep-select") << "...Choose " << r_best << std::endl;
      d_int_rep[r] = r_best;
      if( r_best!=a ){
        Trace("internal-rep-debug") << "rep( " << a << " ) = " << r << ", " << std::endl;
        Trace("internal-rep-debug") << "int_rep( " << a << " ) = " << r_best << ", " << std::endl;
      }
      return r_best;
    }else{
      return d_int_rep[r];
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
  for( std::map< Node, Node >::iterator it = d_int_rep.begin(); it != d_int_rep.end(); ++it ){
    Trace("internal-rep-flatten") << it->first.getType() << " : irep( " << it->first << " ) = " << it->second << std::endl;
  }
  //store representatives for newly created terms
  std::map< Node, Node > temp_rep_map;

  bool success;
  do {
    success = false;
    for( std::map< Node, Node >::iterator it = d_int_rep.begin(); it != d_int_rep.end(); ++it ){
      if( it->second.getKind()==APPLY_UF && it->second.getType().isSort() ){
        Node ni = it->second;
        std::vector< Node > cc;
        cc.push_back( it->second.getOperator() );
        bool changed = false;
        for( unsigned j=0; j<ni.getNumChildren(); j++ ){
          if( ni[j].getType().isSort() ){
            Node r = getRepresentative( ni[j] );
            if( d_int_rep.find( r )==d_int_rep.end() ){
              Assert( temp_rep_map.find( r )!=temp_rep_map.end() );
              r = temp_rep_map[r];
            }
            if( r==ni ){
              //found sub-term as instance
              Trace("internal-rep-flatten-debug") << "...Changed " << it->second << " to subterm " << ni[j] << std::endl;
              d_int_rep[it->first] = ni[j];
              changed = false;
              success = true;
              break;
            }else{
              Node ir = d_int_rep[r];
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
          d_int_rep[it->first] = n;
          temp_rep_map[n] = it->first;
        }
      }
    }
  }while( success );
  Trace("internal-rep-flatten") << "---After flattening : " << std::endl;
  for( std::map< Node, Node >::iterator it = d_int_rep.begin(); it != d_int_rep.end(); ++it ){
    Trace("internal-rep-flatten") << it->first.getType() << " : irep( " << it->first << " ) = " << it->second << std::endl;
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

int getDepth( Node n ){
  if( n.getNumChildren()==0 ){
    return 0;
  }else{
    int maxDepth = -1;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      int depth = getDepth( n[i] );
      if( depth>maxDepth ){
        maxDepth = depth;
      }
    }
    return maxDepth;
  }
}

//smaller the score, the better
int EqualityQueryQuantifiersEngine::getRepScore( Node n, Node f, int index ){
  int s;
  if( options::lteRestrictInstClosure() && ( !d_qe->getTermDatabase()->isInstClosure( n ) || !d_qe->getTermDatabase()->hasTermCurrent( n, false ) ) ){
    return -1;
  }else if( options::instMaxLevel()!=-1 ){
    //score prefer lowest instantiation level
    if( n.hasAttribute(InstLevelAttribute()) ){
      s = n.getAttribute(InstLevelAttribute());
    }else{
      s = options::instLevelInputOnly() ? -1 : 0;
    }
  }else{
    //score prefers earliest use of this term as a representative
    s = d_rep_score.find( n )==d_rep_score.end() ? -1 : d_rep_score[n];
  }
  return s;
  //return ( d_rep_score.find( n )==d_rep_score.end() ? 100 : 0 ) + getDepth( n );    //term depth
}


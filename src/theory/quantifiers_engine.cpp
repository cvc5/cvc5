/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: bobot, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of quantifiers engine class
 **/

#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
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
#include "theory/rewriterules/efficient_e_matching.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

QuantifiersEngine::QuantifiersEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_quant_rel( false ){ //currently do not care about relevance
  d_eq_query = new EqualityQueryQuantifiersEngine( this );
  d_term_db = new quantifiers::TermDb( this );
  d_tr_trie = new inst::TriggerTrie;
  d_eem = new EfficientEMatcher( this );
  d_hasAddedLemma = false;

  //the model object
  d_model = new quantifiers::FirstOrderModel( c, "FirstOrderModel" );

  //add quantifiers modules
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    //the instantiation must set incomplete flag unless finite model finding is turned on
    d_inst_engine = new quantifiers::InstantiationEngine( this, !options::finiteModelFind() );
    d_modules.push_back(  d_inst_engine );
  }else{
    d_inst_engine = NULL;
  }
  if( options::finiteModelFind() ){
    d_model_engine = new quantifiers::ModelEngine( c, this );
    d_modules.push_back( d_model_engine );
  }else{
    d_model_engine = NULL;
  }

  //options
  d_optInstCheckDuplicate = true;
  d_optInstMakeRepresentative = true;
  d_optInstAddSplits = false;
  d_optMatchIgnoreModelBasis = false;
  d_optInstLimitActive = false;
  d_optInstLimit = 0;
}

QuantifiersEngine::~QuantifiersEngine(){
  delete d_model_engine;
  delete d_inst_engine;
  delete d_model;
  delete d_term_db;
  delete d_eq_query;
}

Instantiator* QuantifiersEngine::getInstantiator( theory::TheoryId id ){
  return d_te->theoryOf( id )->getInstantiator();
}

context::Context* QuantifiersEngine::getSatContext(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getSatContext();
}

OutputChannel& QuantifiersEngine::getOutputChannel(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getOutputChannel();
}
/** get default valuation for the quantifiers engine */
Valuation& QuantifiersEngine::getValuation(){
  return d_te->theoryOf( THEORY_QUANTIFIERS )->getValuation();
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_time);
  if( e>=Theory::EFFORT_FULL ){
    Trace("quant-engine") << "Quantifiers Engine check, level = " << e << std::endl;
  }

  d_hasAddedLemma = false;
  if( e==Theory::EFFORT_LAST_CALL ){
    //if effort is last call, try to minimize model first
    if( options::finiteModelFind() ){
      //first, check if we can minimize the model further
      if( !((uf::TheoryUF*)getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver()->minimize() ){
        return;
      }
    }
    ++(d_statistics.d_instantiation_rounds_lc);
  }else if( e==Theory::EFFORT_FULL ){
    ++(d_statistics.d_instantiation_rounds);
  }
  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->check( e );
  }
  //build the model if not done so already
  //  this happens if no quantifiers are currently asserted and no model-building module is enabled
  if( options::produceModels() && e==Theory::EFFORT_LAST_CALL && !d_hasAddedLemma && !d_model->isModelSet() ){
    d_te->getModelBuilder()->buildModel( d_model, true );
  }
  if( e>=Theory::EFFORT_FULL ){
    Trace("quant-engine") << "Finished quantifiers engine check." << std::endl;
  }
}

void QuantifiersEngine::registerQuantifier( Node f ){
  if( std::find( d_quants.begin(), d_quants.end(), f )==d_quants.end() ){
    d_quants.push_back( f );

    ++(d_statistics.d_num_quant);
    Assert( f.getKind()==FORALL );
    //make instantiation constants for f
    d_term_db->makeInstantiationConstantsFor( f );
    //register with quantifier relevance
    d_quant_rel.registerQuantifier( f );
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
  }
}

void QuantifiersEngine::registerPattern( std::vector<Node> & pattern) {
  for(std::vector<Node>::iterator p = pattern.begin(); p != pattern.end(); ++p){
    std::set< Node > added;
    getTermDatabase()->addTerm(*p,added);
  }
}

void QuantifiersEngine::assertNode( Node f ){
  Assert( f.getKind()==FORALL );
  d_model->assertQuantifier( f );
  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->assertNode( f );
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

void QuantifiersEngine::resetInstantiationRound( Theory::Effort level ){
  for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
    if( getInstantiator( i ) ){
      getInstantiator( i )->resetInstantiationRound( level );
    }
  }
  getTermDatabase()->reset( level );
}

void QuantifiersEngine::addTermToDatabase( Node n, bool withinQuant ){
  std::set< Node > added;
  getTermDatabase()->addTerm( n, added, withinQuant );
  if( options::efficientEMatching() ){
    d_eem->newTerms( added );
  }
  //added contains also the Node that just have been asserted in this branch
  for( std::set< Node >::iterator i=added.begin(), end=added.end(); i!=end; i++ ){
    if( !withinQuant ){
      d_quant_rel.setRelevance( i->getOperator(), 0 );
    }
  }
}

void QuantifiersEngine::computeTermVector( Node f, InstMatch& m, std::vector< Node >& vars, std::vector< Node >& terms ){
  for( size_t i=0; i<d_term_db->d_inst_constants[f].size(); i++ ){
    Node n = m.getValue( d_term_db->d_inst_constants[f][i] );
    if( !n.isNull() ){
      vars.push_back( f[0][i] );
      terms.push_back( n );
    }
  }
}

bool QuantifiersEngine::addInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms ){
  Assert( f.getKind()==FORALL );
  Assert( !f.hasAttribute(InstConstantAttribute()) );
  Assert( vars.size()==terms.size() );
  Node body = getInstantiation( f, vars, terms );
  //make the lemma
  NodeBuilder<> nb(kind::OR);
  nb << f.notNode() << body;
  Node lem = nb;
  //check for duplication
  if( addLemma( lem ) ){
    Trace("inst") << "*** Instantiate " << f << " with " << std::endl;
    uint64_t maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      if( terms[i].hasAttribute(InstConstantAttribute()) ){
        Debug("inst")<< "***& Bad Instantiate " << f << " with " << std::endl;
        for( int i=0; i<(int)terms.size(); i++ ){
          Debug("inst") << "   " << terms[i] << std::endl;
        }
        Unreachable("Bad instantiation");
      }else{
        Trace("inst") << "   " << terms[i];
        //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
        Trace("inst") << std::endl;
        if( terms[i].hasAttribute(InstLevelAttribute()) ){
          if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
            maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
          }
        }else{
          setInstantiationLevelAttr( terms[i], 0 );
        }
      }
    }
    Trace("inst-debug") << "*** Lemma is " << lem << std::endl;
    setInstantiationLevelAttr( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
    d_statistics.d_total_inst_var += (int)terms.size();
    d_statistics.d_max_instantiation_level.maxAssign( maxInstLevel+1 );
    return true;
  }else{
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
}

void QuantifiersEngine::setInstantiationLevelAttr( Node n, uint64_t level ){
  if( !n.hasAttribute(InstLevelAttribute()) ){
    InstLevelAttribute ila;
    n.setAttribute(ila,level);
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    setInstantiationLevelAttr( n[i], level );
  }
}

Node QuantifiersEngine::getInstantiation( Node f, std::vector< Node >& vars, std::vector< Node >& terms ){
  Node body = f[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
  //process partial instantiation if necessary
  if( d_term_db->d_vars[f].size()!=vars.size() ){
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
  }
  return body;
}

Node QuantifiersEngine::getInstantiation( Node f, InstMatch& m ){
  std::vector< Node > vars;
  std::vector< Node > terms;
  computeTermVector( f, m, vars, terms );
  return getInstantiation( f, vars, terms );
}

bool QuantifiersEngine::existsInstantiation( Node f, InstMatch& m, bool modEq, bool modInst ){
  return d_inst_match_trie[f].existsInstMatch( this, f, m, modEq, modInst );
}

bool QuantifiersEngine::addLemma( Node lem ){
  Debug("inst-engine-debug") << "Adding lemma : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if( d_lemmas_produced.find( lem )==d_lemmas_produced.end() ){
    //d_curr_out->lemma( lem );
    d_lemmas_produced[ lem ] = true;
    d_lemmas_waiting.push_back( lem );
    Debug("inst-engine-debug") << "Added lemma : " << lem << std::endl;
    return true;
  }else{
    Debug("inst-engine-debug") << "Duplicate." << std::endl;
    return false;
  }
}

bool QuantifiersEngine::addInstantiation( Node f, InstMatch& m, bool modEq, bool modInst, bool mkRep ){
  //make sure there are values for each variable we are instantiating
  m.makeComplete( f, this );
  //make it representative, this is helpful for recognizing duplication
  if( mkRep ){
    m.makeRepresentative( this );
  }
  Trace("inst-add") << "Add instantiation: " << m << std::endl;
  //check for duplication modulo equality
  if( !d_inst_match_trie[f].addInstMatch( this, f, m, modEq, modInst ) ){
    Trace("inst-add") << " -> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
  //compute the vector of terms for the instantiation
  std::vector< Node > terms;
  for( size_t i=0; i<d_term_db->d_inst_constants[f].size(); i++ ){
    Node n = m.getValue( d_term_db->d_inst_constants[f][i] );
    Assert( !n.isNull() );
    terms.push_back( n );
  }
  //add the instantiation
  bool addedInst = addInstantiation( f, d_term_db->d_vars[f], terms );
  //report the result
  if( addedInst ){
    Trace("inst-add") << " -> Success." << std::endl;
    return true;
  }else{
    Trace("inst-add") << " -> Lemma already exists." << std::endl;
    return false;
  }
}

bool QuantifiersEngine::addSplit( Node n, bool reqPhase, bool reqPhasePol ){
  n = Rewriter::rewrite( n );
  Node lem = NodeManager::currentNM()->mkNode( OR, n, n.notNode() );
  if( addLemma( lem ) ){
    ++(d_statistics.d_splits);
    Debug("inst") << "*** Add split " << n<< std::endl;
    //if( reqPhase ){
    //  d_curr_out->requirePhase( n, reqPhasePol );
    //}
    return true;
  }
  return false;
}

bool QuantifiersEngine::addSplitEquality( Node n1, Node n2, bool reqPhase, bool reqPhasePol ){
  //Assert( !n1.hasAttribute(InstConstantAttribute()) );
  //Assert( !n2.hasAttribute(InstConstantAttribute()) );
  //Assert( !areEqual( n1, n2 ) );
  //Assert( !areDisequal( n1, n2 ) );
  Kind knd = n1.getType()==NodeManager::currentNM()->booleanType() ? IFF : EQUAL;
  Node fm = NodeManager::currentNM()->mkNode( knd, n1, n2 );
  return addSplit( fm );
}

void QuantifiersEngine::flushLemmas( OutputChannel* out ){
  if( !d_lemmas_waiting.empty() ){
    //take default output channel if none is provided
    d_hasAddedLemma = true;
    for( int i=0; i<(int)d_lemmas_waiting.size(); i++ ){
      if( out ){
        out->lemma( d_lemmas_waiting[i] );
      }
    }
    d_lemmas_waiting.clear();
  }
}

void QuantifiersEngine::getPhaseReqTerms( Node f, std::vector< Node >& nodes ){
  if( options::literalMatchMode()!=quantifiers::LITERAL_MATCH_NONE && d_phase_reqs.find( f )!=d_phase_reqs.end() ){
    // doing literal-based matching (consider polarity of literals)
    for( int i=0; i<(int)nodes.size(); i++ ){
      Node prev = nodes[i];
      bool nodeChanged = false;
      if( d_phase_reqs[f]->isPhaseReq( nodes[i] ) ){
        bool preq = d_phase_reqs[f]->getPhaseReq( nodes[i] );
        nodes[i] = NodeManager::currentNM()->mkNode( IFF, nodes[i], NodeManager::currentNM()->mkConst<bool>(preq) );
        d_term_db->setInstantiationConstantAttr( nodes[i], f );
        nodeChanged = true;
      }
      //else if( qe->isPhaseReqEquality( f, trNodes[i] ) ){
      //  Node req = qe->getPhaseReqEquality( f, trNodes[i] );
      //  trNodes[i] = NodeManager::currentNM()->mkNode( EQUAL, trNodes[i], req );
      //}
      if( nodeChanged ){
        Debug("literal-matching") << "  Make " << prev << " -> " << nodes[i] << std::endl;
        ++(d_statistics.d_lit_phase_req);
      }else{
        ++(d_statistics.d_lit_phase_nreq);
      }
    }
  }else{
    d_statistics.d_lit_phase_nreq += (int)nodes.size();
  }
}
/*
EqualityQuery* QuantifiersEngine::getEqualityQuery(TypeNode t) {
  // Should use skeleton (in order to have the type and the kind
  //  or any needed other information) instead of only the type

  // TheoryId id = Theory::theoryOf(t);
  // inst::EqualityQuery* eq = d_eq_query_arr[id];
  // if(eq == NULL) return d_eq_query_arr[theory::THEORY_UF];
  // else return eq;

  // hack because the generic one is too slow
  // TheoryId id = Theory::theoryOf(t);
  // if( true || id == theory::THEORY_UF){
  //   uf::InstantiatorTheoryUf* ith = static_cast<uf::InstantiatorTheoryUf*>( getInstantiator( theory::THEORY_UF ));
  //   return new uf::EqualityQueryInstantiatorTheoryUf(ith);
  // }
  // inst::EqualityQuery* eq = d_eq_query_arr[id];
  // if(eq == NULL) return d_eq_query_arr[theory::THEORY_UF];
  // else return eq;


  //Currently we use the generic EqualityQuery
  return getEqualityQuery();
}


rrinst::CandidateGenerator* QuantifiersEngine::getRRCanGenClasses() {
  return new GenericCandidateGeneratorClasses(this);
}

rrinst::CandidateGenerator* QuantifiersEngine::getRRCanGenClass() {
  return new GenericCandidateGeneratorClass(this);
}

rrinst::CandidateGenerator* QuantifiersEngine::getRRCanGenClasses(TypeNode t) {
  // TheoryId id = Theory::theoryOf(t);
  // rrinst::CandidateGenerator* eq = getInstantiator(id)->getRRCanGenClasses();
  // if(eq == NULL) return getInstantiator(id)->getRRCanGenClasses();
  // else return eq;
  return getRRCanGenClasses();
}

rrinst::CandidateGenerator* QuantifiersEngine::getRRCanGenClass(TypeNode t) {
  // TheoryId id = Theory::theoryOf(t);
  // rrinst::CandidateGenerator* eq = getInstantiator(id)->getRRCanGenClass();
  // if(eq == NULL) return getInstantiator(id)->getRRCanGenClass();
  // else return eq;
  return getRRCanGenClass();
}
*/

QuantifiersEngine::Statistics::Statistics():
  d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
  d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
  d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
  d_instantiations("QuantifiersEngine::Instantiations_Total", 0),
  d_max_instantiation_level("QuantifiersEngine::Max_Instantiation_Level", 0),
  d_splits("QuantifiersEngine::Total_Splits", 0),
  d_total_inst_var("QuantifiersEngine::Vars_Inst", 0),
  d_total_inst_var_unspec("QuantifiersEngine::Vars_Inst_Unspecified", 0),
  d_inst_unspec("QuantifiersEngine::Unspecified_Inst", 0),
  d_inst_duplicate("QuantifiersEngine::Duplicate_Inst", 0),
  d_lit_phase_req("QuantifiersEngine::lit_phase_req", 0),
  d_lit_phase_nreq("QuantifiersEngine::lit_phase_nreq", 0),
  d_triggers("QuantifiersEngine::Triggers", 0),
  d_simple_triggers("QuantifiersEngine::Triggers_Simple", 0),
  d_multi_triggers("QuantifiersEngine::Triggers_Multi", 0),
  d_multi_trigger_instantiations("QuantifiersEngine::Multi_Trigger_Instantiations", 0),
  d_term_in_termdb("QuantifiersEngine::Term_in_TermDb", 0),
  d_num_mono_candidates("QuantifiersEngine::NumMonoCandidates", 0),
  d_num_mono_candidates_new_term("QuantifiersEngine::NumMonoCandidatesNewTerm", 0),
  d_num_multi_candidates("QuantifiersEngine::NumMultiCandidates", 0),
  d_mono_candidates_cache_hit("QuantifiersEngine::MonoCandidatesCacheHit", 0),
  d_mono_candidates_cache_miss("QuantifiersEngine::MonoCandidatesCacheMiss", 0),
  d_multi_candidates_cache_hit("QuantifiersEngine::MultiCandidatesCacheHit", 0),
  d_multi_candidates_cache_miss("QuantifiersEngine::MultiCandidatesCacheMiss", 0)
{
  StatisticsRegistry::registerStat(&d_num_quant);
  StatisticsRegistry::registerStat(&d_instantiation_rounds);
  StatisticsRegistry::registerStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::registerStat(&d_instantiations);
  StatisticsRegistry::registerStat(&d_max_instantiation_level);
  StatisticsRegistry::registerStat(&d_splits);
  StatisticsRegistry::registerStat(&d_total_inst_var);
  StatisticsRegistry::registerStat(&d_total_inst_var_unspec);
  StatisticsRegistry::registerStat(&d_inst_unspec);
  StatisticsRegistry::registerStat(&d_inst_duplicate);
  StatisticsRegistry::registerStat(&d_lit_phase_req);
  StatisticsRegistry::registerStat(&d_lit_phase_nreq);
  StatisticsRegistry::registerStat(&d_triggers);
  StatisticsRegistry::registerStat(&d_simple_triggers);
  StatisticsRegistry::registerStat(&d_multi_triggers);
  StatisticsRegistry::registerStat(&d_multi_trigger_instantiations);
  StatisticsRegistry::registerStat(&d_term_in_termdb);
  StatisticsRegistry::registerStat(&d_num_mono_candidates);
  StatisticsRegistry::registerStat(&d_num_mono_candidates_new_term);
  StatisticsRegistry::registerStat(&d_num_multi_candidates);
  StatisticsRegistry::registerStat(&d_mono_candidates_cache_hit);
  StatisticsRegistry::registerStat(&d_mono_candidates_cache_miss);
  StatisticsRegistry::registerStat(&d_multi_candidates_cache_hit);
  StatisticsRegistry::registerStat(&d_multi_candidates_cache_miss);
}

QuantifiersEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_num_quant);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds);
  StatisticsRegistry::unregisterStat(&d_instantiation_rounds_lc);
  StatisticsRegistry::unregisterStat(&d_instantiations);
  StatisticsRegistry::unregisterStat(&d_max_instantiation_level);
  StatisticsRegistry::unregisterStat(&d_splits);
  StatisticsRegistry::unregisterStat(&d_total_inst_var);
  StatisticsRegistry::unregisterStat(&d_total_inst_var_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_unspec);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate);
  StatisticsRegistry::unregisterStat(&d_lit_phase_req);
  StatisticsRegistry::unregisterStat(&d_lit_phase_nreq);
  StatisticsRegistry::unregisterStat(&d_triggers);
  StatisticsRegistry::unregisterStat(&d_simple_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_triggers);
  StatisticsRegistry::unregisterStat(&d_multi_trigger_instantiations);
  StatisticsRegistry::unregisterStat(&d_term_in_termdb);
  StatisticsRegistry::unregisterStat(&d_num_mono_candidates);
  StatisticsRegistry::unregisterStat(&d_num_mono_candidates_new_term);
  StatisticsRegistry::unregisterStat(&d_num_multi_candidates);
  StatisticsRegistry::unregisterStat(&d_mono_candidates_cache_hit);
  StatisticsRegistry::unregisterStat(&d_mono_candidates_cache_miss);
  StatisticsRegistry::unregisterStat(&d_multi_candidates_cache_hit);
  StatisticsRegistry::unregisterStat(&d_multi_candidates_cache_miss);
}


bool EqualityQueryQuantifiersEngine::hasTerm( Node a ){
  eq::EqualityEngine* ee = d_qe->getTheoryEngine()->getSharedTermsDatabase()->getEqualityEngine();
  if( ee->hasTerm( a ) ){
    return true;
  }
  for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
    if( d_qe->getInstantiator( i ) ){
      if( d_qe->getInstantiator( i )->hasTerm( a ) ){
        return true;
      }
    }
  }
  return false;
}

Node EqualityQueryQuantifiersEngine::getRepresentative( Node a ){
  eq::EqualityEngine* ee = d_qe->getTheoryEngine()->getSharedTermsDatabase()->getEqualityEngine();
  if( ee->hasTerm( a ) ){
    return ee->getRepresentative( a );
  }
  for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
    if( d_qe->getInstantiator( i ) ){
      if( d_qe->getInstantiator( i )->hasTerm( a ) ){
        return d_qe->getInstantiator( i )->getRepresentative( a );
      }
    }
  }
  return a;
}

bool EqualityQueryQuantifiersEngine::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else{
    eq::EqualityEngine* ee = d_qe->getTheoryEngine()->getSharedTermsDatabase()->getEqualityEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      if( ee->areEqual( a, b ) ){
        return true;
      }
    }
    for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
      if( d_qe->getInstantiator( i ) ){
        if( d_qe->getInstantiator( i )->areEqual( a, b ) ){
          return true;
        }
      }
    }
    //std::cout << "Equal = " << eq_sh << " " << eq_uf << " " << eq_a << " " << eq_dt << std::endl;
    return false;
  }
}

bool EqualityQueryQuantifiersEngine::areDisequal( Node a, Node b ){
  eq::EqualityEngine* ee = d_qe->getTheoryEngine()->getSharedTermsDatabase()->getEqualityEngine();
  if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
    if( ee->areDisequal( a, b, false ) ){
      return true;
    }
  }
  for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
    if( d_qe->getInstantiator( i ) ){
      if( d_qe->getInstantiator( i )->areDisequal( a, b ) ){
        return true;
      }
    }
  }
  return false;
  //std::cout << "Disequal = " << deq_sh << " " << deq_uf << " " << deq_a << " " << deq_dt << std::endl;
}

Node EqualityQueryQuantifiersEngine::getInternalRepresentative( Node a ){
  //for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
  //  if( d_qe->getInstantiator( i ) ){
  //    if( d_qe->getInstantiator( i )->hasTerm( a ) ){
  //      return d_qe->getInstantiator( i )->getInternalRepresentative( a );
  //    }
  //  }
  //}
  //return a;
  return d_qe->getInstantiator( THEORY_UF )->getInternalRepresentative( a );
}

eq::EqualityEngine* EqualityQueryQuantifiersEngine::getEngine(){
  return ((uf::TheoryUF*)d_qe->getTheoryEngine()->theoryOf( THEORY_UF ))->getEqualityEngine();
}

void EqualityQueryQuantifiersEngine::getEquivalenceClass( Node a, std::vector< Node >& eqc ){
  eq::EqualityEngine* ee = d_qe->getTheoryEngine()->getSharedTermsDatabase()->getEqualityEngine();
  if( ee->hasTerm( a ) ){
    Node rep = ee->getRepresentative( a );
    eq::EqClassIterator eqc_iter( rep, ee );
    while( !eqc_iter.isFinished() ){
      eqc.push_back( *eqc_iter );
      eqc_iter++;
    }
  }
  for( theory::TheoryId i=theory::THEORY_FIRST; i<theory::THEORY_LAST; ++i ){
    if( d_qe->getInstantiator( i ) ){
      d_qe->getInstantiator( i )->getEquivalenceClass( a, eqc );
    }
  }
  if( eqc.empty() ){
    eqc.push_back( a );
  }
}

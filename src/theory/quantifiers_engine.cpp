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
#include "theory/rewriterules/efficient_e_matching.h"
#include "theory/rewriterules/rr_trigger.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

QuantifiersEngine::QuantifiersEngine(context::Context* c, context::UserContext* u, TheoryEngine* te):
d_te( te ),
d_quant_rel( false ),
d_lemmas_produced_c(u){
  d_eq_query = new EqualityQueryQuantifiersEngine( this );
  d_term_db = new quantifiers::TermDb( this );
  d_tr_trie = new inst::TriggerTrie;
  d_rr_tr_trie = new rrinst::TriggerTrie;
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

EqualityQuery* QuantifiersEngine::getEqualityQuery() {
  return d_eq_query;
}

//Instantiator* QuantifiersEngine::getInstantiator( theory::TheoryId id ){
//  return d_te->theoryOf( id )->getInstantiator();
//}

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

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_time);
  bool needsCheck = e>=Theory::EFFORT_LAST_CALL;  //always need to check at or above last call
  for( int i=0; i<(int)d_modules.size(); i++ ){
    if( d_modules[i]->needsCheck( e ) ){
      needsCheck = true;
    }
  }
  if( needsCheck ){
    Trace("quant-engine") << "Quantifiers Engine check, level = " << e << std::endl;
    //reset relevant information
    d_hasAddedLemma = false;
    d_term_db->reset( e );
    d_eq_query->reset();
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
  if( d_inst_match_trie.find( f )!=d_inst_match_trie.end() ){
    if( d_inst_match_trie[f]->existsInstMatch( this, f, m, modEq, modInst ) ){
      return true;
    }
  }
  //also check model engine (it may contain instantiations internally)
  if( d_model_engine->getModelBuilder()->existsInstantiation( f, m, modEq, modInst ) ){
    return true;
  }
  return false;
}

bool QuantifiersEngine::addLemma( Node lem ){
  Debug("inst-engine-debug") << "Adding lemma : " << lem << std::endl;
  lem = Rewriter::rewrite(lem);
  if( d_lemmas_produced_c.find( lem )==d_lemmas_produced_c.end() ){
    //d_curr_out->lemma( lem );
    d_lemmas_produced_c[ lem ] = true;
    d_lemmas_waiting.push_back( lem );
    Debug("inst-engine-debug") << "Added lemma : " << lem << std::endl;
    return true;
  }else{
    Debug("inst-engine-debug") << "Duplicate." << std::endl;
    return false;
  }
}

bool QuantifiersEngine::addInstantiation( Node f, InstMatch& m, bool modEq, bool modInst, bool mkRep ){
  Trace("inst-add-debug") << "Add instantiation: " << m << std::endl;
  //make sure there are values for each variable we are instantiating
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Node ic = d_term_db->getInstantiationConstant( f, i );
    Node val = m.getValue( ic );
    if( val.isNull() ){
      val = d_term_db->getFreeVariableForInstConstant( ic );
      Trace("inst-add-debug") << "mkComplete " << val << std::endl;
      m.set( ic, val );
    }
    //make it representative, this is helpful for recognizing duplication
    if( mkRep ){
      //pick the best possible representative for instantiation, based on past use and simplicity of term
      Node r = d_eq_query->getInternalRepresentative( val );
      Trace("inst-add-debug") << "mkRep " << r << " " << val << std::endl;
      m.set( ic, r );
    }
  }
  //check for duplication modulo equality
  inst::CDInstMatchTrie* imt;
  std::map< Node, inst::CDInstMatchTrie* >::iterator it = d_inst_match_trie.find( f );
  if( it!=d_inst_match_trie.end() ){
    imt = it->second;
  }else{
    imt = new CDInstMatchTrie( getUserContext() );
    d_inst_match_trie[f] = imt;
  }
  Trace("inst-add-debug") << "Adding into inst trie" << std::endl;
  if( !imt->addInstMatch( this, f, m, getUserContext(), modEq, modInst ) ){
    Trace("inst-add-debug") << " -> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
  Trace("inst-add-debug") << "compute terms" << std::endl;
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
    Trace("inst-add") << "Added instantiation for " << f << ": " << std::endl;
    Trace("inst-add") << "   " << m << std::endl;
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

eq::EqualityEngine* QuantifiersEngine::getMasterEqualityEngine(){
  return ((quantifiers::TheoryQuantifiers*)getTheoryEngine()->theoryOf( THEORY_QUANTIFIERS ))->getMasterEqualityEngine();
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
  }
  return a;
}

bool EqualityQueryQuantifiersEngine::areEqual( Node a, Node b ){
  if( a==b ){
    return true;
  }else{
    eq::EqualityEngine* ee = getEngine();
    if( ee->hasTerm( a ) && ee->hasTerm( b ) ){
      if( ee->areEqual( a, b ) ){
        return true;
      }
    }
    return false;
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

Node EqualityQueryQuantifiersEngine::getInternalRepresentative( Node a ){
  Node r = getRepresentative( a );
  if( !options::internalReps() ){
    return r;
  }else{
    if( d_int_rep.find( r )==d_int_rep.end() ){
      std::vector< Node > eqc;
      getEquivalenceClass( r, eqc );
      //find best selection for representative
      Node r_best = r;
      int r_best_score = getRepScore( r );
      for( size_t i=0; i<eqc.size(); i++ ){
        int score = getRepScore( eqc[i] );
        //score prefers earliest use of this term as a representative
        if( score>=0 && ( r_best_score<0 || score<r_best_score ) ){
          r_best = eqc[i];
          r_best_score = score;
        }
      }
      //now, make sure that no other member of the class is an instance
      r_best = getInstance( r_best, eqc );
      //store that this representative was chosen at this point
      if( d_rep_score.find( r_best )==d_rep_score.end() ){
        d_rep_score[ r_best ] = d_reset_count;
      }
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

Node EqualityQueryQuantifiersEngine::getInstance( Node n, std::vector< Node >& eqc ){
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    Node nn = getInstance( n[i], eqc );
    if( !nn.isNull() ){
      return nn;
    }
  }
  if( std::find( eqc.begin(), eqc.end(), n )!=eqc.end() ){
    return n;
  }else{
    return Node::null();
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

int EqualityQueryQuantifiersEngine::getRepScore( Node n ){
  return d_rep_score.find( n )==d_rep_score.end() ? -1 : d_rep_score[n];          //initial
  //return ( d_rep_score.find( n )==d_rep_score.end() ? 100 : 0 ) + getDepth( n );    //term depth
}

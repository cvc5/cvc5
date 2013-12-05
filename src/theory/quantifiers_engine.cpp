/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "theory/quantifiers/bounded_integers.h"
#include "theory/quantifiers/rewrite_engine.h"
#include "theory/uf/options.h"

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
  if( options::fmfFullModelCheck() || options::fmfBoundInt() ){
    d_model = new quantifiers::fmcheck::FirstOrderModelFmc( this, c, "FirstOrderModelFmc" );
  }else{
    d_model = new quantifiers::FirstOrderModelIG( c, "FirstOrderModelIG" );
  }

  //add quantifiers modules
  if( !options::finiteModelFind() || options::fmfInstEngine() ){
    //the instantiation must set incomplete flag unless finite model finding is turned on
    d_inst_engine = new quantifiers::InstantiationEngine( this, !options::finiteModelFind() );
    d_modules.push_back(  d_inst_engine );
  }else{
    d_inst_engine = NULL;
  }
  if( options::finiteModelFind()  ){
    d_model_engine = new quantifiers::ModelEngine( c, this );
    d_modules.push_back( d_model_engine );
    if( options::fmfBoundInt() ){
      d_bint = new quantifiers::BoundedIntegers( c, this );
      d_modules.push_back( d_bint );
    }else{
      d_bint = NULL;
    }
  }else{
    d_model_engine = NULL;
    d_bint = NULL;
  }
  if( options::rewriteRulesAsAxioms() ){
    d_rr_engine = new quantifiers::RewriteEngine( c, this );
    d_modules.push_back(d_rr_engine);
  }else{
    d_rr_engine = NULL;
  }

  //options
  d_optInstCheckDuplicate = true;
  d_optInstMakeRepresentative = true;
  d_optInstAddSplits = false;
  d_optMatchIgnoreModelBasis = false;
  d_optInstLimitActive = false;
  d_optInstLimit = 0;
  d_total_inst_count_debug = 0;
}

QuantifiersEngine::~QuantifiersEngine(){
  delete d_model_engine;
  delete d_inst_engine;
  delete d_model;
  delete d_term_db;
  delete d_eq_query;
}

EqualityQueryQuantifiersEngine* QuantifiersEngine::getEqualityQuery() {
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
    if( !getMasterEqualityEngine()->consistent() ){
      Trace("quant-engine") << "Master equality engine not consistent, return." << std::endl;
      return;
    }
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
    if( e==Theory::EFFORT_LAST_CALL && !d_hasAddedLemma ){
      if( options::produceModels() && !d_model->isModelSet() ){
        d_te->getModelBuilder()->buildModel( d_model, true );
      }
      if( Trace.isOn("inst-per-quant") ){
        for( std::map< Node, int >::iterator it = d_total_inst_debug.begin(); it != d_total_inst_debug.end(); ++it ){
          Trace("inst-per-quant") << " * " << it->second << " for " << it->first << std::endl;
        }
      }
    }else{
      if( Trace.isOn("inst-per-quant-round") ){
        for( std::map< Node, int >::iterator it = d_temp_inst_debug.begin(); it != d_temp_inst_debug.end(); ++it ){
          Trace("inst-per-quant-round") << " * " << it->second << " for " << it->first << std::endl;
          d_temp_inst_debug[it->first] = 0;
        }
      }
    }
    Trace("quant-engine") << "Finished quantifiers engine check." << std::endl;
  }
}

void QuantifiersEngine::registerQuantifier( Node f ){
  if( std::find( d_quants.begin(), d_quants.end(), f )==d_quants.end() ){
    Trace("quant") << "Register quantifier : " << f << std::endl;
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
  Assert( vars.size()==terms.size() );
  Node body = getInstantiation( f, vars, terms );
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
    }
    //uint64_t maxInstLevel = 0;
    if( options::cbqi() ){
      for( int i=0; i<(int)terms.size(); i++ ){
        if( quantifiers::TermDb::hasInstConstAttr(terms[i]) ){
          Debug("inst")<< "***& Bad Instantiate " << f << " with " << std::endl;
          for( int i=0; i<(int)terms.size(); i++ ){
            Debug("inst") << "   " << terms[i] << std::endl;
          }
          Unreachable("Bad instantiation");
        }else{
          Trace("inst") << "   " << terms[i];
          //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
          Trace("inst") << std::endl;
          //if( terms[i].hasAttribute(InstLevelAttribute()) ){
            //if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
            //  maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
            //}
          //}else{
            //setInstantiationLevelAttr( terms[i], 0 );
          //}
        }
      }
    }
    Trace("inst-debug") << "*** Lemma is " << lem << std::endl;
    //setInstantiationLevelAttr( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
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

Node QuantifiersEngine::doSubstitute( Node n, std::vector< Node >& terms ){
  if( n.getKind()==INST_CONSTANT ){
    Debug("check-inst") << "Substitute inst constant : " << n << std::endl;
    return terms[n.getAttribute(InstVarNumAttribute())];
  }else if( !quantifiers::TermDb::hasInstConstAttr( n ) ){
    Debug("check-inst") << "No inst const attr : " << n << std::endl;
    return n;
  }else{
    Debug("check-inst") << "Recurse on : " << n << std::endl;
    std::vector< Node > cc;
    if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
      cc.push_back( n.getOperator() );
    }
    for( unsigned i=0; i<n.getNumChildren(); i++ ){
      cc.push_back( doSubstitute( n[i], terms ) );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), cc );
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
    //do optimized version
    Node icb = d_term_db->getInstConstantBody( f );
    body = doSubstitute( icb, terms );
    if( Debug.isOn("check-inst") ){
      Node body2 = f[ 1 ].substitute( vars.begin(), vars.end(), terms.begin(), terms.end() );
      if( body!=body2 ){
        Debug("check-inst") << "Substitution is wrong : " << body << " " << body2 << std::endl;
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
      Node r = d_eq_query->getInternalRepresentative( val, f, i );
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

QuantifiersEngine::Statistics::Statistics():
  d_num_quant("QuantifiersEngine::Num_Quantifiers", 0),
  d_instantiation_rounds("QuantifiersEngine::Rounds_Instantiation_Full", 0),
  d_instantiation_rounds_lc("QuantifiersEngine::Rounds_Instantiation_Last_Call", 0),
  d_instantiations("QuantifiersEngine::Instantiations_Total", 0),
  d_inst_duplicate("QuantifiersEngine::Duplicate_Inst", 0),
  d_inst_duplicate_eq("QuantifiersEngine::Duplicate_Inst_Eq", 0),
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
  StatisticsRegistry::registerStat(&d_inst_duplicate);
  StatisticsRegistry::registerStat(&d_inst_duplicate_eq);
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
  StatisticsRegistry::unregisterStat(&d_inst_duplicate);
  StatisticsRegistry::unregisterStat(&d_inst_duplicate_eq);
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
      if( options::fmfRelevantDomain() && !f.isNull() ){
        Trace("internal-rep-debug") << "Consult relevant domain to mkRep " << r << std::endl;
        r_best = d_qe->getModelEngine()->getRelevantDomain()->getRelevantTerm( f, index, r );
        Trace("internal-rep-debug") << "Returned " << r_best << " " << r << std::endl;
      }else{
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
            //score prefers earliest use of this term as a representative
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
        r_best = getInstance( r_best, eqc );
        //store that this representative was chosen at this point
        if( d_rep_score.find( r_best )==d_rep_score.end() ){
          d_rep_score[ r_best ] = d_reset_count;
        }
        Trace("internal-rep-select") << "...Choose " << r_best << std::endl;
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

int EqualityQueryQuantifiersEngine::getRepScore( Node n, Node f, int index ){
  return d_rep_score.find( n )==d_rep_score.end() ? -1 : d_rep_score[n];          //initial
  //return ( d_rep_score.find( n )==d_rep_score.end() ? 100 : 0 ) + getDepth( n );    //term depth
}


/*********************                                                        */
/*! \file quantifiers_engine.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/instantiation_engine.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/rr_candidate_generator.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::inst;

//#define COMPUTE_RELEVANCE
//#define REWRITE_ASSERTED_QUANTIFIERS

  /** reset instantiation */
void InstStrategy::resetInstantiationRound( Theory::Effort effort ){
  d_no_instantiate_temp.clear();
  d_no_instantiate_temp.insert( d_no_instantiate_temp.begin(), d_no_instantiate.begin(), d_no_instantiate.end() );
  processResetInstantiationRound( effort );
}

/** do instantiation round method */
int InstStrategy::doInstantiation( Node f, Theory::Effort effort, int e ){
  if( shouldInstantiate( f ) ){
    int origLemmas = d_quantEngine->getNumLemmasWaiting();
    int retVal = process( f, effort, e );
    if( d_quantEngine->getNumLemmasWaiting()!=origLemmas ){
      for( int i=0; i<(int)d_priority_over.size(); i++ ){
        d_priority_over[i]->d_no_instantiate_temp.push_back( f );
      }
    }
    return retVal;
  }else{
    return STATUS_UNKNOWN;
  }
}

QuantifiersEngine::QuantifiersEngine(context::Context* c, TheoryEngine* te):
d_te( te ),
d_active( c ){
  d_eq_query = new EqualityQueryQuantifiersEngine( this );
  d_term_db = new quantifiers::TermDb( this );
  d_hasAddedLemma = false;

  //the model object
  d_model = new quantifiers::FirstOrderModel( this, c, "FirstOrderModel" );

  //add quantifiers modules
  if( !Options::current()->finiteModelFind || Options::current()->fmfInstEngine ){
    //the instantiation must set incomplete flag unless finite model finding is turned on
    d_inst_engine = new quantifiers::InstantiationEngine( this, !Options::current()->finiteModelFind );
    d_modules.push_back(  d_inst_engine );
  }else{
    d_inst_engine = NULL;
  }
  if( Options::current()->finiteModelFind ){
    d_model_engine = new quantifiers::ModelEngine( this );
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
  delete(d_term_db);
}

Instantiator* QuantifiersEngine::getInstantiator( theory::TheoryId id ){
  return d_te->getTheory( id )->getInstantiator();
}

context::Context* QuantifiersEngine::getSatContext(){
  return d_te->getTheory( THEORY_QUANTIFIERS )->getSatContext();
}

OutputChannel& QuantifiersEngine::getOutputChannel(){
  return d_te->getTheory( THEORY_QUANTIFIERS )->getOutputChannel();
}
/** get default valuation for the quantifiers engine */
Valuation& QuantifiersEngine::getValuation(){
  return d_te->getTheory( THEORY_QUANTIFIERS )->getValuation();
}

void QuantifiersEngine::check( Theory::Effort e ){
  CodeTimer codeTimer(d_time);

  d_hasAddedLemma = false;
  d_model_set = false;
  if( e==Theory::EFFORT_LAST_CALL ){
    ++(d_statistics.d_instantiation_rounds_lc);
  }else if( e==Theory::EFFORT_FULL ){
    ++(d_statistics.d_instantiation_rounds);
  }
  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->check( e );
  }
  //build the model if not done so already
  //  this happens if no quantifiers are currently asserted and no model-building module is enabled
  if( Options::current()->produceModels && e==Theory::EFFORT_LAST_CALL && !d_hasAddedLemma && !d_model_set ){
    d_te->getModelBuilder()->buildModel( d_model );
  }
}

std::vector<Node> QuantifiersEngine::createInstVariable( std::vector<Node> & vars ){
  std::vector<Node> inst_constant;
  inst_constant.reserve(vars.size());
  for( std::vector<Node>::const_iterator v = vars.begin();
       v != vars.end(); ++v ){
    //make instantiation constants
    Node ic = NodeManager::currentNM()->mkInstConstant( (*v).getType() );
    inst_constant.push_back( ic );
  };
  return inst_constant;
}

void QuantifiersEngine::registerQuantifier( Node f ){
  if( std::find( d_quants.begin(), d_quants.end(), f )==d_quants.end() ){
    d_quants.push_back( f );
    std::vector< Node > quants;
#ifdef REWRITE_ASSERTED_QUANTIFIERS
    //do assertion-time rewriting of quantifier
    Node nf = quantifiers::QuantifiersRewriter::rewriteQuant( f, false, false );
    if( nf!=f ){
      Debug("quantifiers-rewrite") << "*** assert-rewrite " << f << std::endl;
      Debug("quantifiers-rewrite") << " to " << std::endl;
      Debug("quantifiers-rewrite") << nf << std::endl;
      //we will instead register all the rewritten quantifiers
      if( nf.getKind()==FORALL ){
        quants.push_back( nf );
      }else if( nf.getKind()==AND ){
        for( int i=0; i<(int)nf.getNumChildren(); i++ ){
          quants.push_back( nf[i] );
        }
      }else{
        //unhandled: rewrite must go to a quantifier, or conjunction of quantifiers
        Assert( false );
      }
    }else{
      quants.push_back( f );
    }
#else
    quants.push_back( f );
#endif
    for( int q=0; q<(int)quants.size(); q++ ){
      d_quant_rewritten[f].push_back( quants[q] );
      d_rewritten_quant[ quants[q] ] = f;
      ++(d_statistics.d_num_quant);
      Assert( quants[q].getKind()==FORALL );
      //register quantifier
      d_r_quants.push_back( quants[q] );
      //make instantiation constants for quants[q]
      d_term_db->makeInstantiationConstantsFor( quants[q] );
      //compute symbols in quants[q]
      std::vector< Node > syms;
      computeSymbols( quants[q][1], syms );
      d_syms[quants[q]].insert( d_syms[quants[q]].begin(), syms.begin(), syms.end() );
      //set initial relevance
      int minRelevance = -1;
      for( int i=0; i<(int)syms.size(); i++ ){
        d_syms_quants[ syms[i] ].push_back( quants[q] );
        int r = getRelevance( syms[i] );
        if( r!=-1 && ( minRelevance==-1 || r<minRelevance ) ){
          minRelevance = r;
        }
      }
#ifdef COMPUTE_RELEVANCE
      if( minRelevance!=-1 ){
        setRelevance( quants[q], minRelevance+1 );
      }
#endif
      //register with each module
      for( int i=0; i<(int)d_modules.size(); i++ ){
        d_modules[i]->registerQuantifier( quants[q] );
      }
      Node ceBody = d_term_db->getCounterexampleBody( quants[q] );
      generatePhaseReqs( quants[q], ceBody );
      //also register it with the strong solver
      if( Options::current()->finiteModelFind ){
        ((uf::TheoryUF*)d_te->getTheory( THEORY_UF ))->getStrongSolver()->registerQuantifier( quants[q] );
      }
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
  for( int j=0; j<(int)d_quant_rewritten[f].size(); j++ ){
    d_model->d_forall_asserts.push_back( d_quant_rewritten[f][j] );
    for( int i=0; i<(int)d_modules.size(); i++ ){
      d_modules[i]->assertNode( d_quant_rewritten[f][j] );
    }
  }
}

void QuantifiersEngine::propagate( Theory::Effort level ){
  CodeTimer codeTimer(d_time);

  for( int i=0; i<(int)d_modules.size(); i++ ){
    d_modules[i]->propagate( level );
  }
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
    if( Options::current()->efficientEMatching ){
      uf::InstantiatorTheoryUf* d_ith = (uf::InstantiatorTheoryUf*)getInstantiator( THEORY_UF );
      d_ith->newTerms(added);
    }
#ifdef COMPUTE_RELEVANCE
    //added contains also the Node that just have been asserted in this branch
    for( std::set< Node >::iterator i=added.begin(), end=added.end();
         i!=end; i++ ){
      if( !withinQuant ){
        setRelevance( i->getOperator(), 0 );
      }
  }
#endif

}

bool QuantifiersEngine::addLemma( Node lem ){
  //AJR: the following check is necessary until FULL_CHECK is guarenteed after d_out->lemma(...)
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

bool QuantifiersEngine::addInstantiation( Node f, std::vector< Node >& terms )
{
    //Notice() << "***& Instantiate " << f << " with " << std::endl;
    //for( int i=0; i<(int)terms.size(); i++ ){
    //  Notice() << "   " << terms[i] << std::endl;
    //}
  Assert( f.getKind()==FORALL );
  Assert( !f.hasAttribute(InstConstantAttribute()) );
  Assert( d_term_db->d_vars[f].size()==terms.size() && d_term_db->d_vars[f].size()==f[0].getNumChildren() );
  Node body = f[ 1 ].substitute( d_term_db->d_vars[f].begin(), d_term_db->d_vars[f].end(),
                                 terms.begin(), terms.end() );
  NodeBuilder<> nb(kind::OR);
  nb << d_rewritten_quant[f].notNode() << body;
  Node lem = nb;
  if( addLemma( lem ) ){
    //Notice() << "     Added lemma : " << body << std::endl;
    //Notice() << "***& Instantiate " << f << " with " << std::endl;
    //for( int i=0; i<(int)terms.size(); i++ ){
    //  Notice() << "   " << terms[i] << std::endl;
    //}

    //Notice() << "**INST" << std::endl;
    Debug("inst") << "*** Instantiate " << f << " with " << std::endl;
    //Notice() << "*** Instantiate " << f << " with " << std::endl;
    uint64_t maxInstLevel = 0;
    for( int i=0; i<(int)terms.size(); i++ ){
      if( terms[i].hasAttribute(InstConstantAttribute()) ){
        Debug("inst")<< "***& Bad Instantiate " << f << " with " << std::endl;
        for( int i=0; i<(int)terms.size(); i++ ){
          Debug("inst") << "   " << terms[i] << std::endl;
        }
        Unreachable("Bad instantiation");
      }else{
        Debug("inst") << "   " << terms[i];
        //Notice() << "   " << terms[i] << std::endl;
        //Debug("inst-engine") << " " << terms[i].getAttribute(InstLevelAttribute());
        Debug("inst") << std::endl;
        if( terms[i].hasAttribute(InstLevelAttribute()) ){
          if( terms[i].getAttribute(InstLevelAttribute())>maxInstLevel ){
            maxInstLevel = terms[i].getAttribute(InstLevelAttribute());
          }
        }else{
          d_term_db->setInstantiationLevelAttr( terms[i], 0 );
        }
      }
    }
    d_term_db->setInstantiationLevelAttr( body, maxInstLevel+1 );
    ++(d_statistics.d_instantiations);
    d_statistics.d_total_inst_var += (int)terms.size();
    d_statistics.d_max_instantiation_level.maxAssign( maxInstLevel+1 );
    return true;
  }else{
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
}

bool QuantifiersEngine::addInstantiation( Node f, InstMatch& m ){
  m.makeComplete( f, this );
  m.makeRepresentative( this );
  Debug("quant-duplicate") << "After make rep: " << m << std::endl;
  if( !d_inst_match_trie[f].addInstMatch( this, f, m, true ) ){
    Debug("quant-duplicate") << " -> Already exists." << std::endl;
    ++(d_statistics.d_inst_duplicate);
    return false;
  }
  Debug("quant-duplicate") << " -> Does not exist." << std::endl;
  std::vector< Node > match;
  m.computeTermVec( d_term_db->d_inst_constants[f], match );

  //old....
  //m.makeRepresentative( d_eq_query );
  //std::vector< Node > match;
  //m.computeTermVec( this, d_inst_constants[f], match );

  //Notice() << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
  //for( int i=0; i<(int)m->d_match.size(); i++ ){
  //  Notice() << "   " << m->d_match[i] << std::endl;
  //}

  if( addInstantiation( f, match ) ){
    //d_statistics.d_total_inst_var_unspec.setData( d_statistics.d_total_inst_var_unspec.getData() + (int)d_inst_constants[f].size() - m.d_map.size()/2 );
    //if( d_inst_constants[f].size()!=m.d_map.size() ){
    //  //Notice() << "Unspec. " << std::endl;
    //  //Notice() << "*** Instantiate " << m->getQuantifier() << " with " << std::endl;
    //  //for( int i=0; i<(int)m->d_match.size(); i++ ){
    //  //  Notice() << "   " << m->d_match[i] << std::endl;
    //  //}
    //  ++(d_statistics.d_inst_unspec);
    //}
    //if( addSplits ){
    //  for( std::map< Node, Node >::iterator it = m->d_splits.begin(); it != m->d_splits.end(); ++it ){
    //    addSplitEquality( it->first, it->second, true, true );
    //  }
    //}
    return true;
  }
  return false;
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
  if( Options::current()->literalMatchMode!=Options::LITERAL_MATCH_NONE ){
    bool printed = false;
    // doing literal-based matching (consider polarity of literals)
    for( int i=0; i<(int)nodes.size(); i++ ){
      Node prev = nodes[i];
      bool nodeChanged = false;
      if( isPhaseReq( f, nodes[i] ) ){
        bool preq = getPhaseReq( f, nodes[i] );
        nodes[i] = NodeManager::currentNM()->mkNode( IFF, nodes[i], NodeManager::currentNM()->mkConst<bool>(preq) );
        nodeChanged = true;
      }
      //else if( qe->isPhaseReqEquality( f, trNodes[i] ) ){
      //  Node req = qe->getPhaseReqEquality( f, trNodes[i] );
      //  trNodes[i] = NodeManager::currentNM()->mkNode( EQUAL, trNodes[i], req );
      //}
      if( nodeChanged ){
        if( !printed ){
          Debug("literal-matching") << "LitMatch for " << f << ":" << std::endl;
          printed = true;
        }
        Debug("literal-matching") << "  Make " << prev << " -> " << nodes[i] << std::endl;
        Assert( prev.hasAttribute(InstConstantAttribute()) );
        d_term_db->setInstantiationConstantAttr( nodes[i], prev.getAttribute(InstConstantAttribute()) );
        ++(d_statistics.d_lit_phase_req);
      }else{
        ++(d_statistics.d_lit_phase_nreq);
      }
    }
  }else{
    d_statistics.d_lit_phase_nreq += (int)nodes.size();
  }
}

void QuantifiersEngine::computePhaseReqs2( Node n, bool polarity, std::map< Node, int >& phaseReqs ){
  bool newReqPol = false;
  bool newPolarity;
  if( n.getKind()==NOT ){
    newReqPol = true;
    newPolarity = !polarity;
  }else if( n.getKind()==OR || n.getKind()==IMPLIES ){
    if( !polarity ){
      newReqPol = true;
      newPolarity = false;
    }
  }else if( n.getKind()==AND ){
    if( polarity ){
      newReqPol = true;
      newPolarity = true;
    }
  }else{
    int val = polarity ? 1 : -1;
    if( phaseReqs.find( n )==phaseReqs.end() ){
      phaseReqs[n] = val;
    }else if( val!=phaseReqs[n] ){
      phaseReqs[n] = 0;
    }
  }
  if( newReqPol ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( n.getKind()==IMPLIES && i==0 ){
        computePhaseReqs2( n[i], !newPolarity, phaseReqs );
      }else{
        computePhaseReqs2( n[i], newPolarity, phaseReqs );
      }
    }
  }
}

void QuantifiersEngine::computePhaseReqs( Node n, bool polarity, std::map< Node, bool >& phaseReqs ){
  std::map< Node, int > phaseReqs2;
  computePhaseReqs2( n, polarity, phaseReqs2 );
  for( std::map< Node, int >::iterator it = phaseReqs2.begin(); it != phaseReqs2.end(); ++it ){
    if( it->second==1 ){
      phaseReqs[ it->first ] = true;
    }else if( it->second==-1 ){
      phaseReqs[ it->first ] = false;
    }
  }
}

void QuantifiersEngine::generatePhaseReqs( Node f, Node n ){
  computePhaseReqs( n, false, d_phase_reqs[f] );
  Debug("inst-engine-phase-req") << "Phase requirements for " << f << ":" << std::endl;
  //now, compute if any patterns are equality required
  for( std::map< Node, bool >::iterator it = d_phase_reqs[f].begin(); it != d_phase_reqs[f].end(); ++it ){
    Debug("inst-engine-phase-req") << "   " << it->first << " -> " << it->second << std::endl;
    if( it->first.getKind()==EQUAL ){
      if( it->first[0].hasAttribute(InstConstantAttribute()) ){
        if( !it->first[1].hasAttribute(InstConstantAttribute()) ){
          d_phase_reqs_equality_term[f][ it->first[0] ] = it->first[1];
          d_phase_reqs_equality[f][ it->first[0] ] = it->second;
          Debug("inst-engine-phase-req") << "      " << it->first[0] << ( it->second ? " == " : " != " ) << it->first[1] << std::endl;
        }
      }else if( it->first[1].hasAttribute(InstConstantAttribute()) ){
        d_phase_reqs_equality_term[f][ it->first[1] ] = it->first[0];
        d_phase_reqs_equality[f][ it->first[1] ] = it->second;
        Debug("inst-engine-phase-req") << "      " << it->first[1] << ( it->second ? " == " : " != " ) << it->first[0] << std::endl;
      }
    }
  }

}

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

/** compute symbols */
void QuantifiersEngine::computeSymbols( Node n, std::vector< Node >& syms ){
  if( n.getKind()==APPLY_UF ){
    Node op = n.getOperator();
    if( std::find( syms.begin(), syms.end(), op )==syms.end() ){
      syms.push_back( op );
    }
  }
  if( n.getKind()!=FORALL ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      computeSymbols( n[i], syms );
    }
  }
}

/** set relevance */
void QuantifiersEngine::setRelevance( Node s, int r ){
  int rOld = getRelevance( s );
  if( rOld==-1 || r<rOld ){
    d_relevance[s] = r;
    if( s.getKind()==FORALL ){
      for( int i=0; i<(int)d_syms[s].size(); i++ ){
        setRelevance( d_syms[s][i], r );
      }
    }else{
      for( int i=0; i<(int)d_syms_quants[s].size(); i++ ){
        setRelevance( d_syms_quants[s][i], r+1 );
      }
    }
  }
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
  return ((uf::TheoryUF*)d_qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine();
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

inst::EqualityQuery* QuantifiersEngine::getEqualityQuery(TypeNode t) {
  /** Should use skeleton (in order to have the type and the kind
      or any needed other information) instead of only the type */

  // TheoryId id = Theory::theoryOf(t);
  // inst::EqualityQuery* eq = d_eq_query_arr[id];
  // if(eq == NULL) return d_eq_query_arr[theory::THEORY_UF];
  // else return eq;

  /** hack because the generic one is too slow */
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
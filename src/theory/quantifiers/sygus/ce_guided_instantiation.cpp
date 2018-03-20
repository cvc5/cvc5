/*********************                                                        */
/*! \file ce_guided_instantiation.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief counterexample guided instantiation class
 **   This class is the entry point for both synthesis algorithms in Reynolds et al CAV 2015
 **
 **/
#include "theory/quantifiers/sygus/ce_guided_instantiation.h"

#include "options/quantifiers_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "theory/quantifiers/term_util.h"

using namespace CVC4::kind;
using namespace std;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegInstantiation::CegInstantiation( QuantifiersEngine * qe, context::Context* c ) : QuantifiersModule( qe ){
  d_conj = new CegConjecture( qe );
  d_last_inst_si = false;
}

CegInstantiation::~CegInstantiation(){ 
  delete d_conj;
}

bool CegInstantiation::needsCheck( Theory::Effort e ) {
  return e>=Theory::EFFORT_LAST_CALL;
}

QuantifiersModule::QEffort CegInstantiation::needsModel(Theory::Effort e)
{
  return d_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
}

void CegInstantiation::check(Theory::Effort e, QEffort quant_e)
{
  unsigned echeck =
      d_conj->isSingleInvocation() ? QEFFORT_STANDARD : QEFFORT_MODEL;
  if( quant_e==echeck ){
    Trace("cegqi-engine") << "---Counterexample Guided Instantiation Engine---" << std::endl;
    Trace("cegqi-engine-debug") << std::endl;
    bool active = false;
    bool value;
    if( d_quantEngine->getValuation().hasSatValue( d_conj->getConjecture(), value ) ) {
      active = value;
    }else{
      Trace("cegqi-engine-debug") << "...no value for quantified formula." << std::endl;
    }
    Trace("cegqi-engine-debug") << "Current conjecture status : active : " << active << std::endl;
    std::vector< Node > lem;
    if( active && d_conj->needsCheck( lem ) ){
      checkCegConjecture( d_conj );
    }else{
      Trace("cegqi-engine-debug") << "...does not need check." << std::endl;
      for( unsigned i=0; i<lem.size(); i++ ){
        Trace("cegqi-lemma") << "Cegqi::Lemma : check lemma : " << lem[i] << std::endl;
        d_quantEngine->addLemma( lem[i] );
      }
    }
    Trace("cegqi-engine") << "Finished Counterexample Guided Instantiation engine." << std::endl;
  }
}

void CegInstantiation::registerQuantifier( Node q ) {
  if( d_quantEngine->getOwner( q )==this ){ // && d_eval_axioms.find( q )==d_eval_axioms.end() ){
    if( !d_conj->isAssigned() ){
      Trace("cegqi") << "Register conjecture : " << q << std::endl;
      d_conj->assign( q );
    }else{
      Assert( d_conj->getEmbeddedConjecture()==q );
    }
  }else{
    Trace("cegqi-debug") << "Register quantifier : " << q << std::endl;
  }
}

Node CegInstantiation::getNextDecisionRequest( unsigned& priority ) {
  if( d_conj->isAssigned() ){
    Node dec_req = d_conj->getNextDecisionRequest( priority );
    if( !dec_req.isNull() ){
      Trace("cegqi-debug") << "CEGQI : Decide next on : " << dec_req << "..." << std::endl;
      return dec_req;
    }
  }
  return Node::null();
}

void CegInstantiation::checkCegConjecture( CegConjecture * conj ) {
  Node q = conj->getEmbeddedConjecture();
  Node aq = conj->getConjecture();
  if( Trace.isOn("cegqi-engine-debug") ){
    conj->debugPrint("cegqi-engine-debug");
    Trace("cegqi-engine-debug") << std::endl;
  }

  if( !conj->needsRefinement() ){
    Trace("cegqi-engine-debug") << "Do conjecture check..." << std::endl;
    if( conj->isSyntaxGuided() ){
      std::vector< Node > clems;
      conj->doSingleInvCheck( clems );
      if( !clems.empty() ){
        d_last_inst_si = true;
        for( unsigned j=0; j<clems.size(); j++ ){
          Trace("cegqi-lemma") << "Cegqi::Lemma : single invocation instantiation : " << clems[j] << std::endl;
          d_quantEngine->addLemma( clems[j] );
        }
        d_statistics.d_cegqi_si_lemmas += clems.size();
        Trace("cegqi-engine") << "  ...try single invocation." << std::endl;
        return;
      }
      
      Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
      std::vector< Node > cclems;
      conj->doCheck(cclems);
      bool addedLemma = false;
      for( unsigned i=0; i<cclems.size(); i++ ){
        Node lem = cclems[i];
        d_last_inst_si = false;
        Trace("cegqi-lemma") << "Cegqi::Lemma : counterexample : " << lem << std::endl;
        if( d_quantEngine->addLemma( lem ) ){
          ++(d_statistics.d_cegqi_lemmas_ce);
          addedLemma = true;
        }else{
          //this may happen if we eagerly unfold, simplify to true
          if( !options::sygusDirectEval() ){
            Trace("cegqi-warn") << "  ...FAILED to add candidate!" << std::endl;
          }else{
            Trace("cegqi-engine-debug") << "  ...FAILED to add candidate!" << std::endl;
          }
        }
      }
      if( addedLemma ){
        Trace("cegqi-engine") << "  ...check for counterexample." << std::endl;
      }else{
        if( conj->needsRefinement() ){
          //immediately go to refine candidate
          checkCegConjecture( conj );
          return;
        }
      } 
    }else{
      Assert( aq==q );
      Trace("cegqi-engine") << "  *** Check candidate phase (non-SyGuS)." << std::endl;
      std::vector< Node > lems;
      conj->doBasicCheck(lems);
      Assert(lems.empty());
    }
  }else{
    Trace("cegqi-engine") << "  *** Refine candidate phase..." << std::endl;
    std::vector< Node > rlems;
    conj->doRefine( rlems );
    bool addedLemma = false;
    for( unsigned i=0; i<rlems.size(); i++ ){
      Node lem = rlems[i];
      Trace("cegqi-lemma") << "Cegqi::Lemma : candidate refinement : " << lem << std::endl;
      bool res = d_quantEngine->addLemma( lem );
      if( res ){
        ++(d_statistics.d_cegqi_lemmas_refine);
        conj->incrementRefineCount();
        addedLemma = true;
      }else{
        Trace("cegqi-warn") << "  ...FAILED to add refinement!" << std::endl;
      }
    }
    if( addedLemma ){
      Trace("cegqi-engine") << "  ...refine candidate." << std::endl;
    }
  }
}

void CegInstantiation::printSynthSolution( std::ostream& out ) {
  if( d_conj->isAssigned() )
  {
    d_conj->printSynthSolution( out, d_last_inst_si );
  }
  else
  {
    Assert( false );
  }
}

void CegInstantiation::getSynthSolutions(std::map<Node, Node>& sol_map)
{
  if (d_conj->isAssigned())
  {
    d_conj->getSynthSolutions(sol_map, d_last_inst_si);
  }
  else
  {
    Assert(false);
  }
}

void CegInstantiation::preregisterAssertion( Node n ) {
  //check if it sygus conjecture
  if( QuantAttributes::checkSygusConjecture( n ) ){
    //this is a sygus conjecture
    Trace("cegqi") << "Preregister sygus conjecture : " << n << std::endl;
    d_conj->preregisterConjecture( n );
  }
}

CegInstantiation::Statistics::Statistics()
    : d_cegqi_lemmas_ce("CegInstantiation::cegqi_lemmas_ce", 0),
      d_cegqi_lemmas_refine("CegInstantiation::cegqi_lemmas_refine", 0),
      d_cegqi_si_lemmas("CegInstantiation::cegqi_lemmas_si", 0),
      d_solutions("CegConjecture::solutions", 0),
      d_candidate_rewrites_print("CegConjecture::candidate_rewrites_print", 0),
      d_candidate_rewrites("CegConjecture::candidate_rewrites", 0)

{
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->registerStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->registerStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->registerStat(&d_solutions);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->registerStat(&d_candidate_rewrites);
}

CegInstantiation::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_ce);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_lemmas_refine);
  smtStatisticsRegistry()->unregisterStat(&d_cegqi_si_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_solutions);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites_print);
  smtStatisticsRegistry()->unregisterStat(&d_candidate_rewrites);
}

}/* namespace CVC4::theory::quantifiers */
}/* namespace CVC4::theory */
}/* namespace CVC4 */

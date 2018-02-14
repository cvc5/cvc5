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
//FIXME : remove this include (github issue #1156)
#include "theory/bv/theory_bv_rewriter.h"

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
      //ignore return value here
      std::vector< Node > clist;
      conj->getCandidateList( clist );
      std::vector< Node > model_values;
      conj->getModelValues( clist, model_values );
      if( options::sygusDirectEval() ){
        bool addedEvalLemmas = false;
        if( options::sygusCRefEval() ){
          Trace("cegqi-engine") << "  *** Do conjecture refinement evaluation..." << std::endl;
          // see if any refinement lemma is refuted by evaluation
          std::vector< Node > cre_lems;
          getCRefEvaluationLemmas( conj, clist, model_values, cre_lems );
          if( !cre_lems.empty() ){
            for( unsigned j=0; j<cre_lems.size(); j++ ){
              Node lem = cre_lems[j];
              if( d_quantEngine->addLemma( lem ) ){
                Trace("cegqi-lemma") << "Cegqi::Lemma : cref evaluation : " << lem << std::endl;
                addedEvalLemmas = true;
              }
            }
            if( addedEvalLemmas ){
              //return;
            }
          }
        }
        Trace("cegqi-engine") << "  *** Do direct evaluation..." << std::endl;
        std::vector< Node > eager_terms; 
        std::vector< Node > eager_vals; 
        std::vector< Node > eager_exps;
        for( unsigned j=0; j<clist.size(); j++ ){
          Trace("cegqi-debug") << "  register " << clist[j] << " -> " << model_values[j] << std::endl;
          d_quantEngine->getTermDatabaseSygus()->registerModelValue( clist[j], model_values[j], eager_terms, eager_vals, eager_exps );
        }
        Trace("cegqi-debug") << "...produced " << eager_terms.size()  << " eager evaluation lemmas." << std::endl;
        if( !eager_terms.empty() ){
          for( unsigned j=0; j<eager_terms.size(); j++ ){
            Node lem = NodeManager::currentNM()->mkNode( kind::OR, eager_exps[j].negate(), eager_terms[j].eqNode( eager_vals[j] ) );
            if( d_quantEngine->getTheoryEngine()->isTheoryEnabled(THEORY_BV) ){
              //FIXME: hack to incorporate hacks from BV for division by zero (github issue #1156)
              lem = bv::TheoryBVRewriter::eliminateBVSDiv( lem );
            }
            if( d_quantEngine->addLemma( lem ) ){
              Trace("cegqi-lemma") << "Cegqi::Lemma : evaluation : " << lem << std::endl;
              addedEvalLemmas = true;
            }
          }
        }
        if( addedEvalLemmas ){
          return;
        }
      }
      
      Trace("cegqi-engine") << "  *** Check candidate phase..." << std::endl;
      std::vector< Node > cclems;
      conj->doCheck( cclems, model_values );
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

void CegInstantiation::getCRefEvaluationLemmas( CegConjecture * conj, std::vector< Node >& vs, std::vector< Node >& ms, std::vector< Node >& lems ) {
  Trace("sygus-cref-eval") << "Cref eval : conjecture has " << conj->getNumRefinementLemmas() << " refinement lemmas." << std::endl;
  unsigned nlemmas = conj->getNumRefinementLemmas();
  if (nlemmas > 0 || options::cegisSample() != CEGIS_SAMPLE_NONE)
  {
    Assert( vs.size()==ms.size() );

    TermDbSygus* tds = d_quantEngine->getTermDatabaseSygus();
    Node nfalse = d_quantEngine->getTermUtil()->d_false;
    Node neg_guard = conj->getGuard().negate();
    for (unsigned i = 0; i <= nlemmas; i++)
    {
      if (i == nlemmas)
      {
        bool addedSample = false;
        // find a new one by sampling, if applicable
        if (options::cegisSample() != CEGIS_SAMPLE_NONE)
        {
          addedSample = conj->sampleAddRefinementLemma(ms, lems);
        }
        if (!addedSample)
        {
          return;
        }
      }
      Node lem;
      std::map< Node, Node > visited;
      std::map< Node, std::vector< Node > > exp;
      lem = conj->getRefinementLemma(i);
      if( !lem.isNull() ){
        std::vector< Node > lem_conj;
        //break into conjunctions
        if( lem.getKind()==kind::AND ){
          for( unsigned i=0; i<lem.getNumChildren(); i++ ){
            lem_conj.push_back( lem[i] );
          }
        }else{
          lem_conj.push_back( lem );
        }
        EvalSygusInvarianceTest vsit;
        for( unsigned j=0; j<lem_conj.size(); j++ ){
          Node lemc = lem_conj[j];
          Trace("sygus-cref-eval") << "Check refinement lemma conjunct " << lemc << " against current model." << std::endl;
          Trace("sygus-cref-eval2") << "Check refinement lemma conjunct " << lemc << " against current model." << std::endl;
          Node cre_lem;
          Node lemcs = lemc.substitute( vs.begin(), vs.end(), ms.begin(), ms.end() );
          Trace("sygus-cref-eval2") << "...under substitution it is : " << lemcs << std::endl;
          Node lemcsu = vsit.doEvaluateWithUnfolding(tds, lemcs);
          Trace("sygus-cref-eval2") << "...after unfolding is : " << lemcsu << std::endl;
          if( lemcsu==d_quantEngine->getTermUtil()->d_false ){
            std::vector< Node > msu;
            std::vector< Node > mexp;
            msu.insert( msu.end(), ms.begin(), ms.end() );
            for( unsigned k=0; k<vs.size(); k++ ){
              vsit.setUpdatedTerm(msu[k]);
              msu[k] = vs[k];
              // substitute for everything except this
              Node sconj =
                  lemc.substitute(vs.begin(), vs.end(), msu.begin(), msu.end());
              vsit.init(sconj, vs[k], nfalse);
              // get minimal explanation for this
              Node ut = vsit.getUpdatedTerm();
              Trace("sygus-cref-eval2-debug")
                  << "  compute min explain of : " << vs[k] << " = " << ut
                  << std::endl;
              d_quantEngine->getTermDatabaseSygus()
                  ->getExplain()
                  ->getExplanationFor(vs[k], ut, mexp, vsit);
              msu[k] = ut;
            }
            if( !mexp.empty() ){
              Node en = mexp.size()==1 ? mexp[0] : NodeManager::currentNM()->mkNode( kind::AND, mexp );
              cre_lem = NodeManager::currentNM()->mkNode( kind::OR, en.negate(), neg_guard );
            }else{
              cre_lem = neg_guard;
            }
          }
          if( !cre_lem.isNull() ){
            if( std::find( lems.begin(), lems.end(), cre_lem )==lems.end() ){
              Trace("sygus-cref-eval") << "...produced lemma : " << cre_lem << std::endl;
              lems.push_back( cre_lem );
            }
          }
        }
      }
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

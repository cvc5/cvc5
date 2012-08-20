/*********************                                                        */
/*! \file model_engine.cpp
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
 ** \brief Implementation of model engine class
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/rep_set_iterator.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/quantifiers/options.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

//#define ME_PRINT_WARNINGS

#define EVAL_FAIL_SKIP_MULTIPLE
//#define ONE_QUANT_PER_ROUND

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

//Model Engine constructor
ModelEngine::ModelEngine( QuantifiersEngine* qe ) :
QuantifiersModule( qe ),
d_builder( qe ),
d_rel_domain( qe->getModel() ){

}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL && !d_quantEngine->hasAddedLemma() ){
    //first, check if we can minimize the model further
    if( !((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver()->minimize() ){
      return;
    }
    //the following will attempt to build a model and test that it satisfies all asserted universal quantifiers
    int addedLemmas = 0;
    if( d_builder.optUseModel() ){
      //check if any quantifiers are un-initialized
      for( int i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
        addedLemmas += initializeQuantifier( f );
      }
    }
    if( addedLemmas==0 ){
      //quantifiers are initialized, we begin an instantiation round
      double clSet = 0;
      if( Trace.isOn("model-engine") ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Trace("model-engine") << "---Model Engine Round---" << std::endl;
      }
      Debug("fmf-model-debug") << "---Begin Instantiation Round---" << std::endl;
      ++(d_statistics.d_inst_rounds);
      //reset the quantifiers engine
      d_quantEngine->resetInstantiationRound( e );
      //initialize the model
      Debug("fmf-model-debug") << "Build model..." << std::endl;
      d_builder.buildModel( d_quantEngine->getModel() );
      d_quantEngine->d_model_set = true;
      //if builder has lemmas, add and return
      if( d_builder.d_addedLemmas>0 ){
        addedLemmas += (int)d_builder.d_addedLemmas;
      }else{
        //print debug
        Debug("fmf-model-complete") << std::endl;
        debugPrint("fmf-model-complete");
        //verify we are SAT by trying exhaustive instantiation
        if( optUseRelevantDomain() ){
          d_rel_domain.compute();
        }
        d_triedLemmas = 0;
        d_testLemmas = 0;
        d_relevantLemmas = 0;
        d_totalLemmas = 0;
        Debug("fmf-model-debug") << "Do exhaustive instantiation..." << std::endl;
        for( int i=0; i<d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
          Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
          if( d_builder.d_quant_sat.find( f )==d_builder.d_quant_sat.end() ){
            addedLemmas += exhaustiveInstantiate( f, optUseRelevantDomain() );
            if( optOneQuantPerRound() && addedLemmas>0 ){
              break;
            }
          }
#ifdef ME_PRINT_WARNINGS
          if( addedLemmas>10000 ){
            break;
          }
#endif
        }
        Debug("fmf-model-debug") << "---> Added lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
        Debug("fmf-model-debug") << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
        if( Trace.isOn("model-engine") ){
          Trace("model-engine") << "Added Lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
          Trace("model-engine") << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
          double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
          Trace("model-engine") << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
        }
#ifdef ME_PRINT_WARNINGS
        if( addedLemmas>10000 ){
          Debug("fmf-exit") << std::endl;
          debugPrint("fmf-exit");
          exit( 0 );
        }
#endif
      }
    }
    if( addedLemmas==0 ){
      //CVC4 will answer SAT
      Debug("fmf-consistent") << std::endl;
      debugPrint("fmf-consistent");
      // finish building the model in the standard way
      d_builder.finishProcessBuildModel( d_quantEngine->getModel() );
    }else{
      //otherwise, the search will continue
      d_quantEngine->flushLemmas( &d_quantEngine->getOutputChannel() );
    }
  }
}

void ModelEngine::registerQuantifier( Node f ){

}

void ModelEngine::assertNode( Node f ){

}

bool ModelEngine::optOneInstPerQuantRound(){
  return options::fmfOneInstPerRound();
}

bool ModelEngine::optUseRelevantDomain(){
  return options::fmfRelevantDomain();
}

bool ModelEngine::optOneQuantPerRound(){
#ifdef ONE_QUANT_PER_ROUND
  return true;
#else
  return false;
#endif
}

int ModelEngine::initializeQuantifier( Node f ){
  if( d_quant_init.find( f )==d_quant_init.end() ){
    d_quant_init[f] = true;
    Debug("inst-fmf-init") << "Initialize " << f << std::endl;
    //add the model basis instantiation
    // This will help produce the necessary information for model completion.
    // We do this by extending distinguish ground assertions (those
    //   containing terms with "model basis" attribute) to hold for all cases.

    ////first, check if any variables are required to be equal
    //for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
    //    it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
    //  Node n = it->first;
    //  if( n.getKind()==EQUAL && n[0].getKind()==INST_CONSTANT && n[1].getKind()==INST_CONSTANT ){
    //    Notice() << "Unhandled phase req: " << n << std::endl;
    //  }
    //}
    std::vector< Node > ics;
    std::vector< Node > terms;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      Node t = d_quantEngine->getTermDatabase()->getModelBasisTerm( ic.getType() );
      ics.push_back( ic );
      terms.push_back( t );
      //calculate the basis match for f
      d_builder.d_quant_basis_match[f].set( ic, t);
    }
    ++(d_statistics.d_num_quants_init);
    //register model basis body
    Node n = d_quantEngine->getTermDatabase()->getCounterexampleBody( f );
    Node gn = n.substitute( ics.begin(), ics.end(), terms.begin(), terms.end() );
    d_quantEngine->getTermDatabase()->registerModelBasis( n, gn );
    //add model basis instantiation
    if( d_quantEngine->addInstantiation( f, terms ) ){
      return 1;
    }else{
      //shouldn't happen usually, but will occur if x != y is a required literal for f.
      //Notice() << "No model basis for " << f << std::endl;
      ++(d_statistics.d_num_quants_init_fail);
    }
  }
  return 0;
}

int ModelEngine::exhaustiveInstantiate( Node f, bool useRelInstDomain ){
  int tests = 0;
  int addedLemmas = 0;
  int triedLemmas = 0;
  Debug("inst-fmf-ei") << "Add matches for " << f << "..." << std::endl;
  Debug("inst-fmf-ei") << "   Instantiation Constants: ";
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Debug("inst-fmf-ei") << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i ) << " ";
  }
  Debug("inst-fmf-ei") << std::endl;
  if( d_builder.d_quant_selection_lits[f].empty() ){
    Debug("inst-fmf-ei") << "WARNING: " << f << " has no model literal definitions (is f clausified?)" << std::endl;
#ifdef ME_PRINT_WARNINGS
    Message() << "WARNING: " << f << " has no model literal definitions (is f clausified?)" << std::endl;
#endif
  }else{
    Debug("inst-fmf-ei") << "  Model literal definitions:" << std::endl;
    for( size_t i=0; i<d_builder.d_quant_selection_lits[f].size(); i++ ){
      Debug("inst-fmf-ei") << "    " << d_builder.d_quant_selection_lits[f][i] << std::endl;
    }
  }
  RepSetIterator riter( f, d_quantEngine->getModel() );
  //set the domain for the iterator (the sufficient set of instantiations to try)
  if( useRelInstDomain ){
    riter.setDomain( d_rel_domain.d_quant_inst_domain[f] );
  }
  RepSetEvaluator reval( d_quantEngine->getModel(), &riter );
  while( !riter.isFinished() && ( addedLemmas==0 || !optOneInstPerQuantRound() ) ){
    d_testLemmas++;
    if( d_builder.optUseModel() ){
      //see if instantiation is already true in current model
      Debug("fmf-model-eval") << "Evaluating ";
      riter.debugPrintSmall("fmf-model-eval");
      Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
      tests++;
      //if evaluate(...)==1, then the instantiation is already true in the model
      //  depIndex is the index of the least significant variable that this evaluation relies upon
      int depIndex = riter.getNumTerms()-1;
      int eval = reval.evaluate( d_quantEngine->getTermDatabase()->getCounterexampleBody( f ), depIndex );
      if( eval==1 ){
        Debug("fmf-model-eval") << "  Returned success with depIndex = " << depIndex << std::endl;
        riter.increment2( depIndex );
      }else{
        Debug("fmf-model-eval") << "  Returned " << (eval==-1 ? "failure" : "unknown") << ", depIndex = " << depIndex << std::endl;
        InstMatch m;
        riter.getMatch( d_quantEngine, m );
        Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
        triedLemmas++;
        d_triedLemmas++;
        if( d_quantEngine->addInstantiation( f, m ) ){
          addedLemmas++;
#ifdef EVAL_FAIL_SKIP_MULTIPLE
          if( eval==-1 ){
            riter.increment2( depIndex );
          }else{
            riter.increment();
          }
#else
          riter.increment();
#endif
        }else{
          Debug("ajr-temp") << "* Failed Add instantiation " << m << std::endl;
          riter.increment();
        }
      }
    }else{
      InstMatch m;
      riter.getMatch( d_quantEngine, m );
      Debug("fmf-model-eval") << "* Add instantiation " << std::endl;
      triedLemmas++;
      d_triedLemmas++;
      if( d_quantEngine->addInstantiation( f, m ) ){
        addedLemmas++;
      }
      riter.increment();
    }
  }
  d_statistics.d_eval_formulas += reval.d_eval_formulas;
  d_statistics.d_eval_uf_terms += reval.d_eval_uf_terms;
  d_statistics.d_eval_lits += reval.d_eval_lits;
  d_statistics.d_eval_lits_unknown += reval.d_eval_lits_unknown;
  int totalInst = 1;
  int relevantInst = 1;
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    totalInst = totalInst * (int)d_quantEngine->getModel()->d_rep_set.d_type_reps[ f[0][i].getType() ].size();
    relevantInst = relevantInst * (int)riter.d_domain[i].size();
  }
  d_totalLemmas += totalInst;
  d_relevantLemmas += relevantInst;
  Debug("inst-fmf-ei") << "Finished: " << std::endl;
  Debug("inst-fmf-ei") << "   Inst Total: " << totalInst << std::endl;
  Debug("inst-fmf-ei") << "   Inst Relevant: " << relevantInst << std::endl;
  Debug("inst-fmf-ei") << "   Inst Tried: " << triedLemmas << std::endl;
  Debug("inst-fmf-ei") << "   Inst Added: " << addedLemmas << std::endl;
  Debug("inst-fmf-ei") << "   # Tests: " << tests << std::endl;
///-----------
#ifdef ME_PRINT_WARNINGS
  if( addedLemmas>1000 ){
    Notice() << "WARNING: many instantiations produced for " << f << ": " << std::endl;
    Notice() << "   Inst Total: " << totalInst << std::endl;
    Notice() << "   Inst Relevant: " << totalRelevant << std::endl;
    Notice() << "   Inst Tried: " << triedLemmas << std::endl;
    Notice() << "   Inst Added: " << addedLemmas << std::endl;
    Notice() << "   # Tests: " << tests << std::endl;
    Notice() << std::endl;
    if( !d_builder.d_quant_selection_lits[f].empty() ){
      Notice() << "  Model literal definitions:" << std::endl;
      for( size_t i=0; i<d_builder.d_quant_selection_lits[f].size(); i++ ){
        Notice() << "    " << d_builder.d_quant_selection_lits[f][i] << std::endl;
      }
      Notice() << std::endl;
    }
  }
#endif
///-----------
  return addedLemmas;
}

void ModelEngine::debugPrint( const char* c ){
  Debug( c ) << "Quantifiers: " << std::endl;
  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Debug( c ) << "   ";
    if( d_builder.d_quant_sat.find( f )!=d_builder.d_quant_sat.end() ){
      Debug( c ) << "*SAT* ";
    }else{
      Debug( c ) << "      ";
    }
    Debug( c ) << f << std::endl;
  }
  //d_quantEngine->getModel()->debugPrint( c );
}

ModelEngine::Statistics::Statistics():
  d_inst_rounds("ModelEngine::Inst_Rounds", 0),
  d_eval_formulas("ModelEngine::Eval_Formulas", 0 ),
  d_eval_uf_terms("ModelEngine::Eval_Uf_Terms", 0 ),
  d_eval_lits("ModelEngine::Eval_Lits", 0 ),
  d_eval_lits_unknown("ModelEngine::Eval_Lits_Unknown", 0 ),
  d_num_quants_init("ModelEngine::Num_Quants", 0 ),
  d_num_quants_init_fail("ModelEngine::Num_Quants_No_Basis", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_eval_lits);
  StatisticsRegistry::registerStat(&d_eval_lits_unknown);
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_quants_init_fail);
}

ModelEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_eval_lits);
  StatisticsRegistry::unregisterStat(&d_eval_lits_unknown);
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_quants_init_fail);
}



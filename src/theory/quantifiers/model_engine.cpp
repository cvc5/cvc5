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
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/quantifiers/options.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"

//#define ME_PRINT_WARNINGS

#define EVAL_FAIL_SKIP_MULTIPLE

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

//Model Engine constructor
ModelEngine::ModelEngine( context::Context* c, QuantifiersEngine* qe ) :
QuantifiersModule( qe ),
d_builder( c, qe ),
d_rel_domain( qe, qe->getModel() ){

}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL && !d_quantEngine->hasAddedLemma() ){
    FirstOrderModel* fm = d_quantEngine->getModel();
    //the following will attempt to build a model and test that it satisfies all asserted universal quantifiers
    int addedLemmas = 0;
    Trace("model-engine") << "---Model Engine Round---" << std::endl;
    if( d_builder.optUseModel() ){
      //check if any quantifiers are un-initialized
      for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
        Node f = fm->getAssertedQuantifier( i );
        addedLemmas += initializeQuantifier( f );
      }
    }
    if( addedLemmas>0 ){
      Trace("model-engine") << "Initialize, Added Lemmas = " << addedLemmas << std::endl;
    }
    //two effort levels: first try exhaustive instantiation without axioms, then with.
    int startEffort = ( !fm->isAxiomAsserted() || options::axiomInstMode()==AXIOM_INST_MODE_DEFAULT ) ? 1 : 0;
    for( int effort=startEffort; effort<2; effort++ ){
      // for effort = 0, we only instantiate non-axioms
      // for effort = 1, we instantiate everything
      if( addedLemmas==0 ){
        //quantifiers are initialized, we begin an instantiation round
        double clSet = 0;
        if( Trace.isOn("model-engine") ){
          clSet = double(clock())/double(CLOCKS_PER_SEC);
        }
        ++(d_statistics.d_inst_rounds);
        //reset the quantifiers engine
        d_quantEngine->resetInstantiationRound( e );
        //initialize the model
        Trace("model-engine-debug") << "Build model..." << std::endl;
        d_builder.setEffort( effort );
        d_builder.buildModel( fm, false );
        //if builder has lemmas, add and return
        if( d_builder.d_addedLemmas>0 ){
          addedLemmas += (int)d_builder.d_addedLemmas;
        }else{
          Trace("model-engine-debug") << "Verify uf ss is minimal..." << std::endl;
          //let the strong solver verify that the model is minimal
          uf::StrongSolverTheoryUf* uf_ss = ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver();
          //for debugging, this will if there are terms in the model that the strong solver was not notified of
          uf_ss->debugModel( fm );
          Trace("model-engine-debug") << "Check model..." << std::endl;
          //print debug
          Debug("fmf-model-complete") << std::endl;
          debugPrint("fmf-model-complete");
          //successfully built an acceptable model, now check it
          checkModel( addedLemmas );
          //print debug information
          if( Trace.isOn("model-engine") ){
            Trace("model-engine") << "Instantiate axioms : " << ( d_builder.d_considerAxioms ? "yes" : "no" ) << std::endl;
            Trace("model-engine") << "Added Lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
            Trace("model-engine") << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
            double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
            Trace("model-engine") << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
          }
        }
      }
      if( addedLemmas==0 ){
        //if we have not added lemmas yet and axiomInstMode=trust, then we are done
        if( options::axiomInstMode()==AXIOM_INST_MODE_TRUST ){
          //we must return unknown if an axiom is asserted
          if( effort==0 ){
            d_incomplete_check = true;
          }
          break;
        }
      }
    }
    if( addedLemmas==0 ){
      Trace("model-engine-debug") << "No lemmas added, incomplete = " << d_incomplete_check << std::endl;
      //CVC4 will answer SAT or unknown
      Trace("fmf-consistent") << std::endl;
      debugPrint("fmf-consistent");
      if( options::produceModels() ){
        // finish building the model in the standard way
        d_builder.buildModel( fm, true );
        d_quantEngine->d_model_set = true;
      }
      //if the check was incomplete, we must set incomplete flag
      if( d_incomplete_check ){
        d_quantEngine->getOutputChannel().setIncomplete();
      }
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
  return options::fmfOneQuantPerRound();
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
    std::vector< Node > vars;
    std::vector< Node > ics;
    std::vector< Node > terms;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      Node ic = d_quantEngine->getTermDatabase()->getInstantiationConstant( f, j );
      Node t = d_quantEngine->getTermDatabase()->getModelBasisTerm( ic.getType() );
      vars.push_back( f[0][j] );
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
    if( d_builder.optInstGen() ){
      //add model basis instantiation
      if( d_quantEngine->addInstantiation( f, vars, terms ) ){
        return 1;
      }else{
        //shouldn't happen usually, but will occur if x != y is a required literal for f.
        //Notice() << "No model basis for " << f << std::endl;
        ++(d_statistics.d_num_quants_init_fail);
      }
    }
  }
  return 0;
}

void ModelEngine::checkModel( int& addedLemmas ){
  FirstOrderModel* fm = d_quantEngine->getModel();
  //for debugging
  if( Trace.isOn("model-engine") ){
    for( std::map< TypeNode, std::vector< Node > >::iterator it = fm->d_rep_set.d_type_reps.begin(); it != fm->d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        Trace("model-engine") << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
        Trace("model-engine-debug") << "   ";
        for( size_t i=0; i<it->second.size(); i++ ){
          Trace("model-engine-debug") << it->second[i] << "  ";
        }
        Trace("model-engine-debug") << std::endl;
      }
    }
  }
  //verify we are SAT by trying exhaustive instantiation
  d_incomplete_check = false;
  if( optUseRelevantDomain() ){
    d_rel_domain.compute();
  }
  d_triedLemmas = 0;
  d_testLemmas = 0;
  d_relevantLemmas = 0;
  d_totalLemmas = 0;
  Debug("fmf-model-debug") << "Do exhaustive instantiation..." << std::endl;
  for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    addedLemmas += exhaustiveInstantiate( f, optUseRelevantDomain() );
#ifdef ME_PRINT_WARNINGS
    if( addedLemmas>10000 ){
      Debug("fmf-exit") << std::endl;
      debugPrint("fmf-exit");
      exit( 0 );
    }
#endif
    if( optOneQuantPerRound() && addedLemmas>0 ){
      break;
    }
  }
  Debug("fmf-model-debug") << "---> Added lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
  Debug("fmf-model-debug") << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
}

int ModelEngine::exhaustiveInstantiate( Node f, bool useRelInstDomain ){
  int addedLemmas = 0;
  //keep track of total instantiations for statistics
  int totalInst = 1;
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    TypeNode tn = f[0][i].getType();
    if( d_quantEngine->getModel()->d_rep_set.hasType( tn ) ){
      totalInst = totalInst * (int)d_quantEngine->getModel()->d_rep_set.d_type_reps[ tn ].size();
    }
  }
  d_totalLemmas += totalInst;
  //if we need to consider this quantifier on this iteration
  if( d_builder.isQuantifierActive( f ) ){
    Trace("rel-dom") << "Exhaustive instantiate " << f << std::endl;
    if( useRelInstDomain ){
      Trace("rel-dom") << "Relevant domain : " << std::endl;
      for( size_t i=0; i<d_rel_domain.d_quant_inst_domain[f].size(); i++ ){
        Trace("rel-dom") << "   " << i << " : ";
        for( size_t j=0; j<d_rel_domain.d_quant_inst_domain[f][i].size(); j++ ){
          Trace("rel-dom") << d_rel_domain.d_quant_inst_domain[f][i][j] << " ";
        }
        Trace("rel-dom") << std::endl;
      }
    }
    int tests = 0;
    int triedLemmas = 0;
    Debug("inst-fmf-ei") << "Add matches for " << f << "..." << std::endl;
    Debug("inst-fmf-ei") << "   Instantiation Constants: ";
    for( size_t i=0; i<f[0].getNumChildren(); i++ ){
      Debug("inst-fmf-ei") << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i ) << " ";
    }
    Debug("inst-fmf-ei") << std::endl;
    RepSetIterator riter( &(d_quantEngine->getModel()->d_rep_set) );
    riter.setQuantifier( f );
    //if the iterator is incomplete, we will return unknown instead of sat if no instantiations are added this round
    d_incomplete_check = d_incomplete_check || riter.d_incomplete;
    //set the domain for the iterator (the sufficient set of instantiations to try)
    if( useRelInstDomain ){
      riter.setDomain( d_rel_domain.d_quant_inst_domain[f] );
    }
    d_quantEngine->getModel()->resetEvaluate();
    while( !riter.isFinished() && ( addedLemmas==0 || !optOneInstPerQuantRound() ) ){
      d_testLemmas++;
      int eval = 0;
      int depIndex;
      if( d_builder.optUseModel() ){
        //see if instantiation is already true in current model
        Debug("fmf-model-eval") << "Evaluating ";
        riter.debugPrintSmall("fmf-model-eval");
        Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
        tests++;
        //if evaluate(...)==1, then the instantiation is already true in the model
        //  depIndex is the index of the least significant variable that this evaluation relies upon
        depIndex = riter.getNumTerms()-1;
        eval = d_quantEngine->getModel()->evaluate( d_quantEngine->getTermDatabase()->getCounterexampleBody( f ), depIndex, &riter );
        if( eval==1 ){
          Debug("fmf-model-eval") << "  Returned success with depIndex = " << depIndex << std::endl;
        }else{
          Debug("fmf-model-eval") << "  Returned " << (eval==-1 ? "failure" : "unknown") << ", depIndex = " << depIndex << std::endl;
        }
      }
      if( eval==1 ){
        //instantiation is already true -> skip
        riter.increment2( depIndex );
      }else{
        //instantiation was not shown to be true, construct the match
        InstMatch m;
        for( int i=0; i<riter.getNumTerms(); i++ ){
          m.set( d_quantEngine->getTermDatabase()->getInstantiationConstant( f, riter.d_index_order[i] ), riter.getTerm( i ) );
        }
        Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
        triedLemmas++;
        d_triedLemmas++;
        //add as instantiation
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
    }
    d_statistics.d_eval_formulas += d_quantEngine->getModel()->d_eval_formulas;
    d_statistics.d_eval_uf_terms += d_quantEngine->getModel()->d_eval_uf_terms;
    d_statistics.d_eval_lits += d_quantEngine->getModel()->d_eval_lits;
    d_statistics.d_eval_lits_unknown += d_quantEngine->getModel()->d_eval_lits_unknown;
    int relevantInst = 1;
    for( size_t i=0; i<f[0].getNumChildren(); i++ ){
      relevantInst = relevantInst * (int)riter.d_domain[i].size();
    }
    d_relevantLemmas += relevantInst;
    Debug("inst-fmf-ei") << "Finished: " << std::endl;
    Debug("inst-fmf-ei") << "   Inst Total: " << totalInst << std::endl;
    Debug("inst-fmf-ei") << "   Inst Relevant: " << relevantInst << std::endl;
    Debug("inst-fmf-ei") << "   Inst Tried: " << triedLemmas << std::endl;
    Debug("inst-fmf-ei") << "   Inst Added: " << addedLemmas << std::endl;
    Debug("inst-fmf-ei") << "   # Tests: " << tests << std::endl;
#ifdef ME_PRINT_WARNINGS
    if( addedLemmas>1000 ){
      Notice() << "WARNING: many instantiations produced for " << f << ": " << std::endl;
      Notice() << "   Inst Total: " << totalInst << std::endl;
      Notice() << "   Inst Relevant: " << totalRelevant << std::endl;
      Notice() << "   Inst Tried: " << triedLemmas << std::endl;
      Notice() << "   Inst Added: " << addedLemmas << std::endl;
      Notice() << "   # Tests: " << tests << std::endl;
      Notice() << std::endl;
    }
#endif
  }
  return addedLemmas;
}

void ModelEngine::debugPrint( const char* c ){
  Trace( c ) << "Quantifiers: " << std::endl;
  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Trace( c ) << "   ";
    if( !d_builder.isQuantifierActive( f ) ){
      Trace( c ) << "*Inactive* ";
    }else{
      Trace( c ) << "           ";
    }
    Trace( c ) << f << std::endl;
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



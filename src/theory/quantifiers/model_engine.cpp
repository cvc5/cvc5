/*********************                                                        */
/*! \file model_engine.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
#include "theory/quantifiers/options.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"

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
d_rel_domain( qe, qe->getModel() ){

  if( options::fmfNewInstGen() ){
    d_builder = new ModelEngineBuilderInstGen( c, qe );
  }else{
    d_builder = new ModelEngineBuilderDefault( c, qe );
  }

}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL && !d_quantEngine->hasAddedLemma() ){
    FirstOrderModel* fm = d_quantEngine->getModel();
    //the following will attempt to build a model and test that it satisfies all asserted universal quantifiers
    int addedLemmas = 0;
    //quantifiers are initialized, we begin an instantiation round
    double clSet = 0;
    if( Trace.isOn("model-engine") ){
      clSet = double(clock())/double(CLOCKS_PER_SEC);
    }
    ++(d_statistics.d_inst_rounds);
    //two effort levels: first try exhaustive instantiation without axioms, then with.
    int startEffort = ( !fm->isAxiomAsserted() || options::axiomInstMode()==AXIOM_INST_MODE_DEFAULT ) ? 1 : 0;
    for( int effort=startEffort; effort<2; effort++ ){
      // for effort = 0, we only instantiate non-axioms
      // for effort = 1, we instantiate everything
      if( addedLemmas==0 ){
        Trace("model-engine") << "---Model Engine Round---" << std::endl;
        //initialize the model
        Trace("model-engine-debug") << "Build model..." << std::endl;
        d_builder->setEffort( effort );
        d_builder->buildModel( fm, false );
        addedLemmas += (int)d_builder->d_addedLemmas;
        //if builder has lemmas, add and return
        if( addedLemmas==0 ){
          Trace("model-engine-debug") << "Verify uf ss is minimal..." << std::endl;
          //let the strong solver verify that the model is minimal
          //for debugging, this will if there are terms in the model that the strong solver was not notified of
          ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->theoryOf( THEORY_UF ))->getStrongSolver()->debugModel( fm );
          Trace("model-engine-debug") << "Check model..." << std::endl;
          d_incomplete_check = false;
          //print debug
          Debug("fmf-model-complete") << std::endl;
          debugPrint("fmf-model-complete");
          //successfully built an acceptable model, now check it
          addedLemmas += checkModel( check_model_full );
        }else if( d_builder->didInstGen() && d_builder->optExhInstNonInstGenQuant() ){
          Trace("model-engine-debug") << "Check model for non-inst gen quantifiers..." << std::endl;
          //check quantifiers that inst-gen didn't apply to
          addedLemmas += checkModel( check_model_no_inst_gen );
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
    if( Trace.isOn("model-engine") ){
      double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
      Trace("model-engine") << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
    }
    if( addedLemmas==0 ){
      Trace("model-engine-debug") << "No lemmas added, incomplete = " << d_incomplete_check << std::endl;
      //CVC4 will answer SAT or unknown
      Trace("fmf-consistent") << std::endl;
      debugPrint("fmf-consistent");
      if( options::produceModels() ){
        // finish building the model
        d_builder->buildModel( fm, true );
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

bool ModelEngine::optExhInstEvalSkipMultiple(){
#ifdef EVAL_FAIL_SKIP_MULTIPLE
  return true;
#else
  return false;
#endif
}

int ModelEngine::checkModel( int checkOption ){
  int addedLemmas = 0;
  FirstOrderModel* fm = d_quantEngine->getModel();
  //for debugging
  if( Trace.isOn("model-engine") || Trace.isOn("model-engine-debug") ){
    for( std::map< TypeNode, std::vector< Node > >::iterator it = fm->d_rep_set.d_type_reps.begin();
         it != fm->d_rep_set.d_type_reps.end(); ++it ){
      if( it->first.isSort() ){
        Trace("model-engine") << "Cardinality( " << it->first << " )" << " = " << it->second.size() << std::endl;
        Trace("model-engine-debug") << "   ";
        for( size_t i=0; i<it->second.size(); i++ ){
          //Trace("model-engine-debug") << it->second[i] << "  ";
          Node r = ((EqualityQueryQuantifiersEngine*)d_quantEngine->getEqualityQuery())->getRepresentative( it->second[i] );
          Trace("model-engine-debug") << r << " ";
        }
        Trace("model-engine-debug") << std::endl;
      }
    }
  }
  //compute the relevant domain if necessary
  if( optUseRelevantDomain() ){
    d_rel_domain.compute();
  }
  d_triedLemmas = 0;
  d_testLemmas = 0;
  d_relevantLemmas = 0;
  d_totalLemmas = 0;
  Trace("model-engine-debug") << "Do exhaustive instantiation..." << std::endl;
  for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    //keep track of total instantiations for statistics
    int totalInst = 1;
    for( size_t i=0; i<f[0].getNumChildren(); i++ ){
      TypeNode tn = f[0][i].getType();
      if( fm->d_rep_set.hasType( tn ) ){
        totalInst = totalInst * (int)fm->d_rep_set.d_type_reps[ tn ].size();
      }
    }
    d_totalLemmas += totalInst;
    //determine if we should check this quantifiers
    bool checkQuant = false;
    if( checkOption==check_model_full ){
      checkQuant = d_builder->isQuantifierActive( f );
    }else if( checkOption==check_model_no_inst_gen ){
      checkQuant = !d_builder->hasInstGen( f );
    }
    //if we need to consider this quantifier on this iteration
    if( checkQuant ){
      addedLemmas += exhaustiveInstantiate( f, optUseRelevantDomain() );
      if( Trace.isOn("model-engine-warn") ){
        if( addedLemmas>10000 ){
          Debug("fmf-exit") << std::endl;
          debugPrint("fmf-exit");
          exit( 0 );
        }
      }
      if( optOneQuantPerRound() && addedLemmas>0 ){
        break;
      }
    }
  }
  //print debug information
  if( Trace.isOn("model-engine") ){
    Trace("model-engine") << "Instantiate axioms : " << ( d_builder->d_considerAxioms ? "yes" : "no" ) << std::endl;
    Trace("model-engine") << "Added Lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
    Trace("model-engine") << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
  }
  d_statistics.d_exh_inst_lemmas += addedLemmas;
  return addedLemmas;
}

int ModelEngine::exhaustiveInstantiate( Node f, bool useRelInstDomain ){
  int addedLemmas = 0;
  Trace("inst-fmf-ei") << "Exhaustive instantiate " << f << "..." << std::endl;
  Debug("inst-fmf-ei") << "   Instantiation Constants: ";
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Debug("inst-fmf-ei") << d_quantEngine->getTermDatabase()->getInstantiationConstant( f, i ) << " ";
  }
  Debug("inst-fmf-ei") << std::endl;

  //create a rep set iterator and iterate over the (relevant) domain of the quantifier
  RepSetIterator riter( &(d_quantEngine->getModel()->d_rep_set) );
  if( riter.setQuantifier( f ) ){
    //set the domain for the iterator (the sufficient set of instantiations to try)
    if( useRelInstDomain ){
      riter.setDomain( d_rel_domain.d_quant_inst_domain[f] );
    }
    d_quantEngine->getModel()->resetEvaluate();
    int tests = 0;
    int triedLemmas = 0;
    while( !riter.isFinished() && ( addedLemmas==0 || !optOneInstPerQuantRound() ) ){
      d_testLemmas++;
      int eval = 0;
      int depIndex;
      if( d_builder->optUseModel() ){
        //see if instantiation is already true in current model
        Debug("fmf-model-eval") << "Evaluating ";
        riter.debugPrintSmall("fmf-model-eval");
        Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
        tests++;
        //if evaluate(...)==1, then the instantiation is already true in the model
        //  depIndex is the index of the least significant variable that this evaluation relies upon
        depIndex = riter.getNumTerms()-1;
        eval = d_quantEngine->getModel()->evaluate( d_quantEngine->getTermDatabase()->getInstConstantBody( f ), depIndex, &riter );
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
          //if the instantiation is show to be false, and we wish to skip multiple instantiations at once
          if( eval==-1 && optExhInstEvalSkipMultiple() ){
            riter.increment2( depIndex );
          }else{
            riter.increment();
          }
        }else{
          Debug("fmf-model-eval") << "* Failed Add instantiation " << m << std::endl;
          riter.increment();
        }
      }
    }
    //print debugging information
    d_statistics.d_eval_formulas += d_quantEngine->getModel()->d_eval_formulas;
    d_statistics.d_eval_uf_terms += d_quantEngine->getModel()->d_eval_uf_terms;
    d_statistics.d_eval_lits += d_quantEngine->getModel()->d_eval_lits;
    d_statistics.d_eval_lits_unknown += d_quantEngine->getModel()->d_eval_lits_unknown;
    int relevantInst = 1;
    for( size_t i=0; i<f[0].getNumChildren(); i++ ){
      relevantInst = relevantInst * (int)riter.d_domain[i].size();
    }
    d_relevantLemmas += relevantInst;
    Trace("inst-fmf-ei") << "Finished: " << std::endl;
    //Debug("inst-fmf-ei") << "   Inst Total: " << totalInst << std::endl;
    Trace("inst-fmf-ei") << "   Inst Relevant: " << relevantInst << std::endl;
    Trace("inst-fmf-ei") << "   Inst Tried: " << triedLemmas << std::endl;
    Trace("inst-fmf-ei") << "   Inst Added: " << addedLemmas << std::endl;
    Trace("inst-fmf-ei") << "   # Tests: " << tests << std::endl;
    if( addedLemmas>1000 ){
      Trace("model-engine-warn") << "WARNING: many instantiations produced for " << f << ": " << std::endl;
      //Trace("model-engine-warn") << "   Inst Total: " << totalInst << std::endl;
      Trace("model-engine-warn") << "   Inst Relevant: " << relevantInst << std::endl;
      Trace("model-engine-warn") << "   Inst Tried: " << triedLemmas << std::endl;
      Trace("model-engine-warn") << "   Inst Added: " << addedLemmas << std::endl;
      Trace("model-engine-warn") << "   # Tests: " << tests << std::endl;
      Trace("model-engine-warn") << std::endl;
    }
  }
   //if the iterator is incomplete, we will return unknown instead of sat if no instantiations are added this round
  d_incomplete_check = d_incomplete_check || riter.d_incomplete;
  return addedLemmas;
}

void ModelEngine::debugPrint( const char* c ){
  Trace( c ) << "Quantifiers: " << std::endl;
  for( int i=0; i<(int)d_quantEngine->getModel()->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getModel()->getAssertedQuantifier( i );
    Trace( c ) << "   ";
    if( !d_builder->isQuantifierActive( f ) ){
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
  d_exh_inst_lemmas("ModelEngine::Exhaustive_Instantiation_Lemmas", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_eval_lits);
  StatisticsRegistry::registerStat(&d_eval_lits_unknown);
  StatisticsRegistry::registerStat(&d_exh_inst_lemmas);
}

ModelEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_eval_lits);
  StatisticsRegistry::unregisterStat(&d_eval_lits_unknown);
  StatisticsRegistry::unregisterStat(&d_exh_inst_lemmas);
}



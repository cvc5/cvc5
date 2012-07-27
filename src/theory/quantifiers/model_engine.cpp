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
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

//#define ME_PRINT_WARNINGS

//#define DISABLE_EVAL_SKIP_MULTIPLE

#define RECONSIDER_FUNC_CONSTANT
#define EVAL_FAIL_SKIP_MULTIPLE
//#define ONE_QUANT_PER_ROUND_INST_GEN
//#define ONE_QUANT_PER_ROUND

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;
using namespace CVC4::theory::inst;

ModelEngineBuilder::ModelEngineBuilder( QuantifiersEngine* qe ) :
TheoryEngineModelBuilder( qe->getTheoryEngine() ),
d_qe( qe ){

}

Node ModelEngineBuilder::chooseRepresentative( TheoryModel* tm, Node eqc ){
  return eqc;
}

void ModelEngineBuilder::processBuildModel( TheoryModel* m ) {
  d_addedLemmas = 0;
  //only construct first order model if optUseModel() is true
  if( optUseModel() ){
    FirstOrderModel* fm = (FirstOrderModel*)m;
    //initialize model
    fm->initialize();
    //analyze the quantifiers
    Debug("fmf-model-debug") << "Analyzing quantifiers..." << std::endl;
    analyzeQuantifiers( fm );
    //if applicable, find exceptions
    if( optInstGen() ){
      //now, see if we know that any exceptions via InstGen exist
      Debug("fmf-model-debug") << "Perform InstGen techniques for quantifiers..." << std::endl;
      for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
        Node f = fm->getAssertedQuantifier( i );
        if( d_quant_sat.find( f )==d_quant_sat.end() ){
          d_addedLemmas += doInstGen( fm, f );
          if( optOneQuantPerRoundInstGen() && d_addedLemmas>0 ){
            break;
          }
        }
      }
      if( Options::current()->printModelEngine ){
        if( d_addedLemmas>0 ){
          Message() << "InstGen, added lemmas = " << d_addedLemmas << std::endl;
        }else{
          Message() << "No InstGen lemmas..." << std::endl;
        }
      }
      Debug("fmf-model-debug") << "---> Added lemmas = " << d_addedLemmas << std::endl;
    }
    if( d_addedLemmas==0 ){
      //if no immediate exceptions, build the model
      //  this model will be an approximation that will need to be tested via exhaustive instantiation
      Debug("fmf-model-debug") << "Building model..." << std::endl;
      finishBuildModel( fm );
    }
  }
}

void ModelEngineBuilder::analyzeQuantifiers( FirstOrderModel* fm ){
  d_quant_selection_lits.clear();
  d_quant_sat.clear();
  d_uf_prefs.clear();
  int quantSatInit = 0;
  int nquantSatInit = 0;
  //analyze the preferences of each quantifier
  for( int i=0; i<(int)fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
    std::vector< Node > pro_con[2];
    std::vector< Node > constantSatOps;
    bool constantSatReconsider;
    //for each asserted quantifier f,
    // - determine which literals form model basis for each quantifier
    // - check which function/predicates have good and bad definitions according to f
    for( std::map< Node, bool >::iterator it = d_qe->d_phase_reqs[f].begin();
         it != d_qe->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Node gn = d_qe->getTermDatabase()->getModelBasis( n );
      Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
      //calculate preference
      int pref = 0;
      bool value;
      if( d_qe->getValuation().hasSatValue( gn, value ) ){
        if( value!=it->second ){
          //store this literal as a model basis literal
          //  this literal will force a default values in model that (modulo exceptions) shows
          //  that f is satisfied by the model
          d_quant_selection_lits[f].push_back( value ? n : n.notNode() );
          pref = 1;
        }else{
          pref = -1;
        }
      }
      if( pref!=0 ){
        //Store preferences for UF
        bool isConst = !n.hasAttribute(InstConstantAttribute());
        std::vector< Node > uf_terms;
        if( gn.getKind()==APPLY_UF ){
          uf_terms.push_back( gn );
          isConst = fm->d_uf_model[gn.getOperator()].isConstant();
        }else if( gn.getKind()==EQUAL ){
          isConst = true;
          for( int j=0; j<2; j++ ){
            if( n[j].hasAttribute(InstConstantAttribute()) ){
              if( n[j].getKind()==APPLY_UF ){
                Node op = gn[j].getOperator();
                if( fm->d_uf_model.find( op )!=fm->d_uf_model.end() ){
                  uf_terms.push_back( gn[j] );
                  isConst = isConst && fm->d_uf_model[op].isConstant();
                }else{
                  isConst = false;
                }
              }else{
                isConst = false;
              }
            }
          }
        }
        Debug("fmf-model-prefs") << "  It is " << ( pref==1 ? "pro" : "con" );
        Debug("fmf-model-prefs") << " the definition of " << n << std::endl;
        if( pref==1 && isConst ){
          d_quant_sat[f] = true;
          //instead, just note to the model for each uf term that f is pro its definition
          constantSatReconsider = false;
          constantSatOps.clear();
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            Node op = uf_terms[j].getOperator();
            constantSatOps.push_back( op );
            if( d_uf_prefs[op].d_reconsiderModel ){
              constantSatReconsider = true;
            }
          }
          if( !constantSatReconsider ){
            break;
          }
        }else{
          int pcIndex = pref==1 ? 0 : 1;
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            pro_con[pcIndex].push_back( uf_terms[j] );
          }
        }
      }
    }
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      Debug("fmf-model-prefs") << "  * Constant SAT due to definition of ops: ";
      for( int i=0; i<(int)constantSatOps.size(); i++ ){
        Debug("fmf-model-prefs") << constantSatOps[i] << " ";
        d_uf_prefs[constantSatOps[i]].d_reconsiderModel = false;
      }
      Debug("fmf-model-prefs") << std::endl;
      quantSatInit++;
      d_statistics.d_pre_sat_quant += quantSatInit;
    }else{
      nquantSatInit++;
      d_statistics.d_pre_nsat_quant += quantSatInit;
      //note quantifier's value preferences to models
      for( int k=0; k<2; k++ ){
        for( int j=0; j<(int)pro_con[k].size(); j++ ){
          Node op = pro_con[k][j].getOperator();
          Node r = fm->getRepresentative( pro_con[k][j] );
          d_uf_prefs[op].setValuePreference( f, pro_con[k][j], r, k==0 );
        }
      }
    }
  }
  Debug("fmf-model-prefs") << "Pre-Model Completion: Quantifiers SAT: " << quantSatInit << " / " << (quantSatInit+nquantSatInit) << std::endl;
}

int ModelEngineBuilder::doInstGen( FirstOrderModel* fm, Node f ){
  //we wish to add all known exceptions to our model basis literal(s)
  //  this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  int addedLemmas = 0;
  for( int i=0; i<(int)d_quant_selection_lits[f].size(); i++ ){
    bool phase = d_quant_selection_lits[f][i].getKind()!=NOT;
    Node lit = d_quant_selection_lits[f][i].getKind()==NOT ? d_quant_selection_lits[f][i][0] : d_quant_selection_lits[f][i];
    Assert( lit.hasAttribute(InstConstantAttribute()) );
    std::vector< Node > tr_terms;
    if( lit.getKind()==APPLY_UF ){
      //only match predicates that are contrary to this one, use literal matching
      Node eq = NodeManager::currentNM()->mkNode( IFF, lit, !phase ? fm->d_true : fm->d_false );
      fm->getTermDatabase()->setInstantiationConstantAttr( eq, f );
      tr_terms.push_back( eq );
    }else if( lit.getKind()==EQUAL ){
      //collect trigger terms
      for( int j=0; j<2; j++ ){
        if( lit[j].hasAttribute(InstConstantAttribute()) ){
          if( lit[j].getKind()==APPLY_UF ){
            tr_terms.push_back( lit[j] );
          }else{
            tr_terms.clear();
            break;
          }
        }
      }
      if( tr_terms.size()==1 && !phase ){
        //equality between a function and a ground term, use literal matching
        tr_terms.clear();
        tr_terms.push_back( lit );
      }
    }
    //if applicable, try to add exceptions here
    if( !tr_terms.empty() ){
      //make a trigger for these terms, add instantiations
      Trigger* tr = Trigger::mkTrigger( d_qe, f, tr_terms );
      //Notice() << "Trigger = " << (*tr) << std::endl;
      tr->resetInstantiationRound();
      tr->reset( Node::null() );
      //d_qe->d_optInstMakeRepresentative = false;
      //d_qe->d_optMatchIgnoreModelBasis = true;
      addedLemmas += tr->addInstantiations( d_quant_basis_match[f] );
    }
  }
  return addedLemmas;
}

void ModelEngineBuilder::finishBuildModel( FirstOrderModel* fm ){
  //build model for UF
  for( std::map< Node, uf::UfModel >::iterator it = fm->d_uf_model.begin(); it != fm->d_uf_model.end(); ++it ){
    finishBuildModelUf( fm, it->second );
  }
  //build model for arrays
  for( std::map< Node, Node >::iterator it = fm->d_array_model.begin(); it != fm->d_array_model.end(); ++it ){
    //consult the model basis select term
    // i.e. the default value for array A is the value of select( A, e ), where e is the model basis term
    TypeNode tn = it->first.getType();
    Node selModelBasis = NodeManager::currentNM()->mkNode( SELECT, it->first, fm->getTermDatabase()->getModelBasisTerm( tn[0] ) );
    it->second = fm->getRepresentative( selModelBasis );
  }
  Debug("fmf-model-debug") << "Done building models." << std::endl;
}

void ModelEngineBuilder::finishBuildModelUf( FirstOrderModel* fm, uf::UfModel& model ){
  Node op = model.getOperator();
#ifdef RECONSIDER_FUNC_CONSTANT
  if( model.isModelConstructed() && model.isConstant() ){
    if( d_uf_prefs[op].d_reconsiderModel ){
      //if we are allowed to reconsider default value, then see if the default value can be improved
      Node t = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
      Node v = model.getConstantValue( t );
      if( d_uf_prefs[op].d_value_pro_con[0][v].empty() ){
        Debug("fmf-model-cons-debug") << "Consider changing the default value for " << op << std::endl;
        model.clearModel();
      }
    }
  }
#endif
  if( !model.isModelConstructed() ){
    //construct the model for the uninterpretted function/predicate
    bool setDefaultVal = true;
    Node defaultTerm = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
    Debug("fmf-model-cons") << "Construct model for " << op << "..." << std::endl;
    //set the values in the model
    for( size_t i=0; i<model.d_ground_asserts.size(); i++ ){
      Node n = model.d_ground_asserts[i];
      Node v = model.d_ground_asserts_reps[i];
      //if this assertion did not help the model, just consider it ground
      //set n = v in the model tree
      Debug("fmf-model-cons") << "  Set " << n << " = ";
      fm->printRepresentativeDebug( "fmf-model-cons", v );
      Debug("fmf-model-cons") << std::endl;
      //set it as ground value
      model.setValue( n, v );
      if( model.optUsePartialDefaults() ){
        //also set as default value if necessary
        //if( n.getAttribute(ModelBasisArgAttribute())==1 && !d_term_pro_con[0][n].empty() ){
        if( n.hasAttribute(ModelBasisArgAttribute()) && n.getAttribute(ModelBasisArgAttribute())==1 ){
          model.setValue( n, v, false );
          if( n==defaultTerm ){
            //incidentally already set, we will not need to find a default value
            setDefaultVal = false;
          }
        }
      }else{
        if( n==defaultTerm ){
          model.setValue( n, v, false );
          //incidentally already set, we will not need to find a default value
          setDefaultVal = false;
        }
      }
    }
    //set the overall default value if not set already  (is this necessary??)
    if( setDefaultVal ){
      Debug("fmf-model-cons") << "  Choose default value..." << std::endl;
      //chose defaultVal based on heuristic, currently the best ratio of "pro" responses
      Node defaultVal = d_uf_prefs[op].getBestDefaultValue( defaultTerm, fm );
      Assert( !defaultVal.isNull() );
      model.setValue( defaultTerm, defaultVal, false );
    }
    Debug("fmf-model-cons") << "  Making model...";
    model.setModel();
    Debug("fmf-model-cons") << "  Finished constructing model for " << op << "." << std::endl;
  }
}

bool ModelEngineBuilder::optUseModel() {
  return Options::current()->fmfModelBasedInst;
}

bool ModelEngineBuilder::optInstGen(){
  return Options::current()->fmfInstGen;
}

bool ModelEngineBuilder::optOneQuantPerRoundInstGen(){
#ifdef ONE_QUANT_PER_ROUND_INST_GEN
  return true;
#else
  return false;
#endif
}

ModelEngineBuilder::Statistics::Statistics():
  d_pre_sat_quant("ModelEngineBuilder::Status_quant_pre_sat", 0),
  d_pre_nsat_quant("ModelEngineBuilder::Status_quant_pre_non_sat", 0)
{
  StatisticsRegistry::registerStat(&d_pre_sat_quant);
  StatisticsRegistry::registerStat(&d_pre_nsat_quant);
}

ModelEngineBuilder::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_pre_sat_quant);
  StatisticsRegistry::unregisterStat(&d_pre_nsat_quant);
}

//Model Engine constructor
ModelEngine::ModelEngine( QuantifiersEngine* qe ) :
QuantifiersModule( qe ),
d_builder( qe ),
d_rel_domain( qe->getModel() ){

}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL && !d_quantEngine->hasAddedLemma() ){
    //first, check if we can minimize the model further
    if( !((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver()->minimize() ){
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
      if( Options::current()->printModelEngine ){
        clSet = double(clock())/double(CLOCKS_PER_SEC);
        Message() << "---Model Engine Round---" << std::endl;
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
        if( Options::current()->printModelEngine ){
          Message() << "Added Lemmas = " << addedLemmas << " / " << d_triedLemmas << " / ";
          Message() << d_testLemmas << " / " << d_relevantLemmas << " / " << d_totalLemmas << std::endl;
          double clSet2 = double(clock())/double(CLOCKS_PER_SEC);
          Message() << "Finished model engine, time = " << (clSet2-clSet) << std::endl;
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
  return Options::current()->fmfOneInstPerRound;
}

bool ModelEngine::optUseRelevantDomain(){
  return Options::current()->fmfRelevantDomain;
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
  d_statistics.d_eval_eqs += reval.d_eval_eqs;
  d_statistics.d_eval_uf_terms += reval.d_eval_uf_terms;
  int totalInst = 1;
  int relevantInst = 1;
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    totalInst = totalInst * (int)d_quantEngine->getModel()->d_ra.d_type_reps[ f[0][i].getType() ].size();
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
  d_eval_eqs("ModelEngine::Eval_Equalities", 0 ),
  d_eval_uf_terms("ModelEngine::Eval_Uf_Terms", 0 ),
  d_num_quants_init("ModelEngine::Num_Quants", 0 ),
  d_num_quants_init_fail("ModelEngine::Num_Quants_No_Basis", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_eqs);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_quants_init_fail);
}

ModelEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_eqs);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_quants_init_fail);
}



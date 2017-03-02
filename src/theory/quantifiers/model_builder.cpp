/*********************                                                        */
/*! \file model_builder.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of model builder class
 **/

#include "theory/quantifiers/model_builder.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/model_engine.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/trigger.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/uf/theory_uf_strong_solver.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;


QModelBuilder::QModelBuilder( context::Context* c, QuantifiersEngine* qe ) :
TheoryEngineModelBuilder( qe->getTheoryEngine() ), d_curr_model( c, NULL ), d_qe( qe ){

}

bool QModelBuilder::optUseModel() {
  return options::mbqiMode()!=MBQI_NONE || options::fmfBound();
}

void QModelBuilder::preProcessBuildModel(TheoryModel* m, bool fullModel) {
  preProcessBuildModelStd( m, fullModel );
}

void QModelBuilder::preProcessBuildModelStd(TheoryModel* m, bool fullModel) {
  if( !fullModel ){
    if( options::fmfEmptySorts() || options::fmfFunWellDefinedRelevant() ){
      FirstOrderModel * fm = (FirstOrderModel*)m;
      //traverse equality engine
      std::map< TypeNode, bool > eqc_usort;
      eq::EqClassesIterator eqcs_i = eq::EqClassesIterator( fm->d_equalityEngine );
      while( !eqcs_i.isFinished() ){
        TypeNode tr = (*eqcs_i).getType();
        eqc_usort[tr] = true;
        ++eqcs_i;
      }
      //look at quantified formulas
      for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
        Node q = fm->getAssertedQuantifier( i, true );
        if( fm->isQuantifierActive( q ) ){
          //check if any of these quantified formulas can be set inactive
          if( options::fmfEmptySorts() ){
            for( unsigned i=0; i<q[0].getNumChildren(); i++ ){
              TypeNode tn = q[0][i].getType();
              //we are allowed to assume the type is empty
              if( tn.isSort() && eqc_usort.find( tn )==eqc_usort.end() ){
                Trace("model-engine-debug") << "Empty domain quantified formula : " << q << std::endl;
                fm->setQuantifierActive( q, false );
              }
            }
          }else if( options::fmfFunWellDefinedRelevant() ){
            if( q[0].getNumChildren()==1 ){
              TypeNode tn = q[0][0].getType();
              if( tn.getAttribute(AbsTypeFunDefAttribute()) ){
                //Trace("model-engine-debug2") << "...possible irrelevant function def : " << q << ", #rr = " << d_quantEngine->getModel()->d_rep_set.getNumRelevantGroundReps( tn ) << std::endl;
                //we are allowed to assume the introduced type is empty
                if( eqc_usort.find( tn )==eqc_usort.end() ){
                  Trace("model-engine-debug") << "Irrelevant function definition : " << q << std::endl;
                  fm->setQuantifierActive( q, false );
                }
              }
            }
          }
        }
      }
    }
  }
}

void QModelBuilder::debugModel( FirstOrderModel* fm ){
  //debug the model: cycle through all instantiations for all quantifiers, report ones that are not true
  if( Trace.isOn("quant-check-model") ){
    Trace("quant-check-model") << "Testing quantifier instantiations..." << std::endl;
    int tests = 0;
    int bad = 0;
    for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node f = fm->getAssertedQuantifier( i );
      std::vector< Node > vars;
      for( unsigned j=0; j<f[0].getNumChildren(); j++ ){
        vars.push_back( f[0][j] );
      }
      RepSetIterator riter( d_qe, &(fm->d_rep_set) );
      if( riter.setQuantifier( f ) ){
        while( !riter.isFinished() ){
          tests++;
          std::vector< Node > terms;
          for( int k=0; k<riter.getNumTerms(); k++ ){
            terms.push_back( riter.getCurrentTerm( k ) );
          }
          Node n = d_qe->getInstantiation( f, vars, terms );
          Node val = fm->getValue( n );
          if( val!=fm->d_true ){
            Trace("quant-check-model") << "*******  Instantiation " << n << " for " << std::endl;
            Trace("quant-check-model") << "         " << f << std::endl;
            Trace("quant-check-model") << "         Evaluates to " << val << std::endl;
            bad++;
          }
          riter.increment();
        }
        Trace("quant-check-model") << "Tested " << tests << " instantiations";
        if( bad>0 ){
          Trace("quant-check-model") << ", " << bad << " failed" << std::endl;
        }
        Trace("quant-check-model") << "." << std::endl;
      }else{
        if( riter.isIncomplete() ){
          Trace("quant-check-model") << "Warning: Could not test quantifier " << f << std::endl;
        }
      }
    }
  }
}



bool TermArgBasisTrie::addTerm2( FirstOrderModel* fm, Node n, int argIndex ){
  if( argIndex<(int)n.getNumChildren() ){
    Node r;
    if( n[ argIndex ].getAttribute(ModelBasisAttribute()) ){
      r = n[ argIndex ];
    }else{
      r = fm->getRepresentative( n[ argIndex ] );
    }
    std::map< Node, TermArgBasisTrie >::iterator it = d_data.find( r );
    if( it==d_data.end() ){
      d_data[r].addTerm2( fm, n, argIndex+1 );
      return true;
    }else{
      return it->second.addTerm2( fm, n, argIndex+1 );
    }
  }else{
    return false;
  }
}


QModelBuilderIG::QModelBuilderIG( context::Context* c, QuantifiersEngine* qe ) :
QModelBuilder( c, qe ), d_basisNoMatch( c ) {

}

Node QModelBuilderIG::getCurrentUfModelValue( FirstOrderModel* fm, Node n, std::vector< Node > & args, bool partial ) {
  return n;
}

void QModelBuilderIG::processBuildModel( TheoryModel* m, bool fullModel ) {
  FirstOrderModel* f = (FirstOrderModel*)m;
  FirstOrderModelIG* fm = f->asFirstOrderModelIG();
  Trace("model-engine-debug") << "Process build model, fullModel = " << fullModel << " " << optUseModel() << std::endl;
  if( fullModel ){
    Assert( d_curr_model==fm );
    //update models
    for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
      it->second.update( fm );
      Trace("model-func") << "QModelBuilder: Make function value from tree " << it->first << std::endl;
      //construct function values
      fm->d_uf_models[ it->first ] = it->second.getFunctionValue( "$x" );
    }
    TheoryEngineModelBuilder::processBuildModel( m, fullModel );
    //mark that the model has been set
    fm->markModelSet();
    //debug the model
    debugModel( fm );
  }else{
    d_curr_model = fm;
    d_didInstGen = false;
    //reset the internal information
    reset( fm );
    //only construct first order model if optUseModel() is true
    if( optUseModel() ){
      Trace("model-engine-debug") << "Initializing " << fm->getNumAssertedQuantifiers() << " quantifiers..." << std::endl;
      //check if any quantifiers are un-initialized
      for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
        Node q = fm->getAssertedQuantifier( i );
        if( d_qe->getModel()->isQuantifierActive( q ) ){
          int lems = initializeQuantifier( q, q );
          d_statistics.d_init_inst_gen_lemmas += lems;
          d_addedLemmas += lems;
          if( d_qe->inConflict() ){
            break;
          }
        }
      }
      if( d_addedLemmas>0 ){
        Trace("model-engine") << "Initialize, Added Lemmas = " << d_addedLemmas << std::endl;
      }else{
        Assert( !d_qe->inConflict() );
        //initialize model
        fm->initialize();
        //analyze the functions
        Trace("model-engine-debug") << "Analyzing model..." << std::endl;
        analyzeModel( fm );
        //analyze the quantifiers
        Trace("model-engine-debug") << "Analyzing quantifiers..." << std::endl;
        d_uf_prefs.clear();
        for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
          Node q = fm->getAssertedQuantifier( i );
          analyzeQuantifier( fm, q );
        }

        //if applicable, find exceptions to model via inst-gen
        if( options::fmfInstGen() ){
          d_didInstGen = true;
          d_instGenMatches = 0;
          d_numQuantSat = 0;
          d_numQuantInstGen = 0;
          d_numQuantNoInstGen = 0;
          d_numQuantNoSelForm = 0;
          //now, see if we know that any exceptions via InstGen exist
          Trace("model-engine-debug") << "Perform InstGen techniques for quantifiers..." << std::endl;
          for( unsigned i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
            Node f = fm->getAssertedQuantifier( i );
            if( d_qe->getModel()->isQuantifierActive( f ) ){
              int lems = doInstGen( fm, f );
              d_statistics.d_inst_gen_lemmas += lems;
              d_addedLemmas += lems;
              //temporary
              if( lems>0 ){
                d_numQuantInstGen++;
              }else if( hasInstGen( f ) ){
                d_numQuantNoInstGen++;
              }else{
                d_numQuantNoSelForm++;
              }
              if( d_qe->inConflict() || ( options::fmfInstGenOneQuantPerRound() && lems>0 ) ){
                break;
              }
            }else{
              d_numQuantSat++;
            }
          }
          Trace("model-engine-debug") << "Quantifiers sat/ig/n-ig/null " << d_numQuantSat << " / " << d_numQuantInstGen << " / ";
          Trace("model-engine-debug") << d_numQuantNoInstGen << " / " << d_numQuantNoSelForm << std::endl;
          Trace("model-engine-debug") << "Inst-gen # matches examined = " << d_instGenMatches << std::endl;
          if( Trace.isOn("model-engine") ){
            if( d_addedLemmas>0 ){
              Trace("model-engine") << "InstGen, added lemmas = " << d_addedLemmas << std::endl;
            }else{
              Trace("model-engine") << "No InstGen lemmas..." << std::endl;
            }
          }
        }
        //construct the model if necessary
        if( d_addedLemmas==0 ){
          //if no immediate exceptions, build the model
          //  this model will be an approximation that will need to be tested via exhaustive instantiation
          Trace("model-engine-debug") << "Building model..." << std::endl;
          //build model for UF
          for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
            Trace("model-engine-debug-uf") << "Building model for " << it->first << "..." << std::endl;
            constructModelUf( fm, it->first );
          }
          Trace("model-engine-debug") << "Done building models." << std::endl;
        }
      }
    }
  }
}

int QModelBuilderIG::initializeQuantifier( Node f, Node fp ){
  if( d_quant_basis_match_added.find( f )==d_quant_basis_match_added.end() ){
    //create the basis match if necessary
    if( d_quant_basis_match.find( f )==d_quant_basis_match.end() ){
      Trace("inst-fmf-init") << "Initialize " << f << std::endl;
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
      d_quant_basis_match[f] = InstMatch( f );
      for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
        Node t = d_qe->getTermDatabase()->getModelBasisTerm( f[0][j].getType() );
        //calculate the basis match for f
        d_quant_basis_match[f].setValue( j, t );
      }
      ++(d_statistics.d_num_quants_init);
    }
    //try to add it
    Trace("inst-fmf-init") << "Init: try to add match " << d_quant_basis_match[f] << std::endl;
    //add model basis instantiation
    if( d_qe->addInstantiation( fp, d_quant_basis_match[f] ) ){
      d_quant_basis_match_added[f] = true;
      return 1;
    }else{
      //shouldn't happen usually, but will occur if x != y is a required literal for f.
      //Notice() << "No model basis for " << f << std::endl;
      d_quant_basis_match_added[f] = false;
    }
  }
  return 0;
}

void QModelBuilderIG::analyzeModel( FirstOrderModel* fm ){
  FirstOrderModelIG* fmig = fm->asFirstOrderModelIG();
  d_uf_model_constructed.clear();
  //determine if any functions are constant
  for( std::map< Node, uf::UfModelTree >::iterator it = fmig->d_uf_model_tree.begin(); it != fmig->d_uf_model_tree.end(); ++it ){
    Node op = it->first;
    TermArgBasisTrie tabt;
    for( size_t i=0; i<fmig->d_uf_terms[op].size(); i++ ){
      Node n = fmig->d_uf_terms[op][i];
      //for calculating if op is constant
      if( d_qe->getTermDatabase()->isTermActive( n ) ){
        Node v = fmig->getRepresentative( n );
        if( i==0 ){
          d_uf_prefs[op].d_const_val = v;
        }else if( v!=d_uf_prefs[op].d_const_val ){
          d_uf_prefs[op].d_const_val = Node::null();
          break;
        }
      }
      //for calculating terms that we don't need to consider
      if( d_qe->getTermDatabase()->isTermActive( n ) || n.getAttribute(ModelBasisArgAttribute())!=0 ){
        if( d_basisNoMatch.find( n )==d_basisNoMatch.end() ){
          //need to consider if it is not congruent modulo model basis
          if( !tabt.addTerm( fmig, n ) ){
            d_basisNoMatch[n] = true;
          }
        }
      }
    }
    if( !d_uf_prefs[op].d_const_val.isNull() ){
      fmig->d_uf_model_gen[op].setDefaultValue( d_uf_prefs[op].d_const_val );
      fmig->d_uf_model_gen[op].makeModel( fmig, it->second );
      Debug("fmf-model-cons") << "Function " << op << " is the constant function ";
      fmig->printRepresentativeDebug( "fmf-model-cons", d_uf_prefs[op].d_const_val );
      Debug("fmf-model-cons") << std::endl;
      d_uf_model_constructed[op] = true;
    }else{
      d_uf_model_constructed[op] = false;
    }
  }
}

bool QModelBuilderIG::hasConstantDefinition( Node n ){
  Node lit = n.getKind()==NOT ? n[0] : n;
  if( lit.getKind()==APPLY_UF ){
    Node op = lit.getOperator();
    if( !d_uf_prefs[op].d_const_val.isNull() ){
      return true;
    }
  }
  return false;
}

QModelBuilderIG::Statistics::Statistics():
  d_num_quants_init("QModelBuilderIG::Number_Quantifiers", 0),
  d_num_partial_quants_init("QModelBuilderIG::Number_Partial_Quantifiers", 0),
  d_init_inst_gen_lemmas("QModelBuilderIG::Initialize_Inst_Gen_Lemmas", 0 ),
  d_inst_gen_lemmas("QModelBuilderIG::Inst_Gen_Lemmas", 0 ),
  d_eval_formulas("QModelBuilderIG::Eval_Formulas", 0 ),
  d_eval_uf_terms("QModelBuilderIG::Eval_Uf_Terms", 0 ),
  d_eval_lits("QModelBuilderIG::Eval_Lits", 0 ),
  d_eval_lits_unknown("QModelBuilderIG::Eval_Lits_Unknown", 0 )
{
  smtStatisticsRegistry()->registerStat(&d_num_quants_init);
  smtStatisticsRegistry()->registerStat(&d_num_partial_quants_init);
  smtStatisticsRegistry()->registerStat(&d_init_inst_gen_lemmas);
  smtStatisticsRegistry()->registerStat(&d_inst_gen_lemmas);
  smtStatisticsRegistry()->registerStat(&d_eval_formulas);
  smtStatisticsRegistry()->registerStat(&d_eval_uf_terms);
  smtStatisticsRegistry()->registerStat(&d_eval_lits);
  smtStatisticsRegistry()->registerStat(&d_eval_lits_unknown);
}

QModelBuilderIG::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_num_quants_init);
  smtStatisticsRegistry()->unregisterStat(&d_num_partial_quants_init);
  smtStatisticsRegistry()->unregisterStat(&d_init_inst_gen_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_inst_gen_lemmas);
  smtStatisticsRegistry()->unregisterStat(&d_eval_formulas);
  smtStatisticsRegistry()->unregisterStat(&d_eval_uf_terms);
  smtStatisticsRegistry()->unregisterStat(&d_eval_lits);
  smtStatisticsRegistry()->unregisterStat(&d_eval_lits_unknown);
}

bool QModelBuilderIG::isTermActive( Node n ){
  return d_qe->getTermDatabase()->isTermActive( n ) || //it is not congruent to another active term
         ( n.getAttribute(ModelBasisArgAttribute())!=0 && d_basisNoMatch.find( n )==d_basisNoMatch.end() ); //or it has model basis arguments
                                                                                                      //and is not congruent modulo model basis
                                                                                                      //to another active term
}

//do exhaustive instantiation
int QModelBuilderIG::doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort ) {
  if( optUseModel() ){
    RepSetIterator riter( d_qe, &(d_qe->getModel()->d_rep_set) );
    if( riter.setQuantifier( f ) ){
      FirstOrderModelIG * fmig = (FirstOrderModelIG*)d_qe->getModel();
      Debug("inst-fmf-ei") << "Reset evaluate..." << std::endl;
      fmig->resetEvaluate();
      Debug("inst-fmf-ei") << "Begin instantiation..." << std::endl;
      while( !riter.isFinished() && ( d_addedLemmas==0 || !options::fmfOneInstPerRound() ) ){
        d_triedLemmas++;
        if( Debug.isOn("inst-fmf-ei-debug") ){
          for( int i=0; i<(int)riter.d_index.size(); i++ ){
            Debug("inst-fmf-ei-debug") << i << " : " << riter.d_index[i] << " : " << riter.getCurrentTerm( i ) << std::endl;
          }
        }
        int eval = 0;
        int depIndex;
        //see if instantiation is already true in current model
        if( Debug.isOn("fmf-model-eval") ){
          Debug("fmf-model-eval") << "Evaluating ";
          riter.debugPrintSmall("fmf-model-eval");
          Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
        }
        //if evaluate(...)==1, then the instantiation is already true in the model
        //  depIndex is the index of the least significant variable that this evaluation relies upon
        depIndex = riter.getNumTerms()-1;
        Debug("fmf-model-eval") << "We will evaluate " << d_qe->getTermDatabase()->getInstConstantBody( f ) << std::endl;
        eval = fmig->evaluate( d_qe->getTermDatabase()->getInstConstantBody( f ), depIndex, &riter );
        if( eval==1 ){
          Debug("fmf-model-eval") << "  Returned success with depIndex = " << depIndex << std::endl;
        }else{
          Debug("fmf-model-eval") << "  Returned " << (eval==-1 ? "failure" : "unknown") << ", depIndex = " << depIndex << std::endl;
        }
        if( eval==1 ){
          //instantiation is already true -> skip
          riter.increment2( depIndex );
        }else{
          //instantiation was not shown to be true, construct the match
          InstMatch m( f );
          for( int i=0; i<riter.getNumTerms(); i++ ){
            m.set( d_qe, i, riter.getCurrentTerm( i ) );
          }
          Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
          //add as instantiation
          if( d_qe->addInstantiation( f, m, true ) ){
            d_addedLemmas++;
            if( d_qe->inConflict() ){
              break;
            }
            //if the instantiation is show to be false, and we wish to skip multiple instantiations at once
            if( eval==-1 ){
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
      if( fmig ){
        d_statistics.d_eval_formulas += fmig->d_eval_formulas;
        d_statistics.d_eval_uf_terms += fmig->d_eval_uf_terms;
        d_statistics.d_eval_lits += fmig->d_eval_lits;
        d_statistics.d_eval_lits_unknown += fmig->d_eval_lits_unknown;
      }
      Trace("inst-fmf-ei") << "For " << f << ", finished: " << std::endl;
      Trace("inst-fmf-ei") << "   Inst Tried: " << d_triedLemmas << std::endl;
      Trace("inst-fmf-ei") << "   Inst Added: " << d_addedLemmas << std::endl;
      if( d_addedLemmas>1000 ){
        Trace("model-engine-warn") << "WARNING: many instantiations produced for " << f << ": " << std::endl;
        Trace("model-engine-warn") << "   Inst Tried: " << d_triedLemmas << std::endl;
        Trace("model-engine-warn") << "   Inst Added: " << d_addedLemmas << std::endl;
        Trace("model-engine-warn") << std::endl;
      }
    }
    //if the iterator is incomplete, we will return unknown instead of sat if no instantiations are added this round
    return riter.isIncomplete() ? -1 : 1;
  }else{
    return 0;
  }
}



void QModelBuilderDefault::reset( FirstOrderModel* fm ){
  d_quant_selection_lit.clear();
  d_quant_selection_lit_candidates.clear();
  d_quant_selection_lit_terms.clear();
  d_term_selection_lit.clear();
  d_op_selection_terms.clear();
}


int QModelBuilderDefault::getSelectionScore( std::vector< Node >& uf_terms ) {
  /*
  size_t maxChildren = 0;
  for( size_t i=0; i<uf_terms.size(); i++ ){
    if( uf_terms[i].getNumChildren()>maxChildren ){
      maxChildren = uf_terms[i].getNumChildren();
    }
  }
  //TODO: look at how many entries they have?
  return (int)maxChildren;
  */
  return 0;
}

void QModelBuilderDefault::analyzeQuantifier( FirstOrderModel* fm, Node f ){
  if( d_qe->getModel()->isQuantifierActive( f ) ){
    FirstOrderModelIG* fmig = fm->asFirstOrderModelIG();
    Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
    //the pro/con preferences for this quantifier
    std::vector< Node > pro_con[2];
    //the terms in the selection literal we choose
    std::vector< Node > selectionLitTerms;
    Trace("inst-gen-debug-quant") << "Inst-gen analyze " << f << std::endl;
    //for each asserted quantifier f,
    // - determine selection literals
    // - check which function/predicates have good and bad definitions for satisfying f
    if( d_phase_reqs.find( f )==d_phase_reqs.end() ){
      d_phase_reqs[f].initialize( d_qe->getTermDatabase()->getInstConstantBody( f ), true );
    }
    int selectLitScore = -1;
    for( std::map< Node, bool >::iterator it = d_phase_reqs[f].d_phase_reqs.begin(); it != d_phase_reqs[f].d_phase_reqs.end(); ++it ){
      //the literal n is phase-required for quantifier f
      Node n = it->first;
      Node gn = d_qe->getTermDatabase()->getModelBasis( f, n );
      Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
      bool value;
      //if the corresponding ground abstraction literal has a SAT value
      if( d_qe->getValuation().hasSatValue( gn, value ) ){
        //collect the non-ground uf terms that this literal contains
        //  and compute if all of the symbols in this literal have
        //  constant definitions.
        bool isConst = true;
        std::vector< Node > uf_terms;
        if( TermDb::hasInstConstAttr(n) ){
          isConst = false;
          if( gn.getKind()==APPLY_UF ){
            uf_terms.push_back( gn );
            isConst = hasConstantDefinition( gn );
          }else if( gn.getKind()==EQUAL ){
            isConst = true;
            for( int j=0; j<2; j++ ){
              if( TermDb::hasInstConstAttr(n[j]) ){
                if( n[j].getKind()==APPLY_UF &&
                    fmig->d_uf_model_tree.find( gn[j].getOperator() )!=fmig->d_uf_model_tree.end() ){
                  uf_terms.push_back( gn[j] );
                  isConst = isConst && hasConstantDefinition( gn[j] );
                }else{
                  isConst = false;
                }
              }
            }
          }
        }
        //check if the value in the SAT solver matches the preference according to the quantifier
        int pref = 0;
        if( value!=it->second ){
          //we have a possible selection literal
          bool selectLit = d_quant_selection_lit[f].isNull();
          bool selectLitConstraints = true;
          //it is a constantly defined selection literal : the quantifier is sat
          if( isConst ){
            selectLit = selectLit || d_qe->getModel()->isQuantifierActive( f );
            d_qe->getModel()->setQuantifierActive( f, false );
            //check if choosing this literal would add any additional constraints to default definitions
            selectLitConstraints = false;
            for( int j=0; j<(int)uf_terms.size(); j++ ){
              Node op = uf_terms[j].getOperator();
              if( d_uf_prefs[op].d_reconsiderModel ){
                selectLitConstraints = true;
              }
            }
            if( !selectLitConstraints ){
              selectLit = true;
            }
          }
          //also check if it is naturally a better literal
          if( !selectLit ){
            int score = getSelectionScore( uf_terms );
            //Trace("inst-gen-debug") << "Check " << score << " < " << selectLitScore << std::endl;
            selectLit = score<selectLitScore;
          }
          //see if we wish to choose this as a selection literal
          d_quant_selection_lit_candidates[f].push_back( value ? n : n.notNode() );
          if( selectLit ){
            selectLitScore = getSelectionScore( uf_terms );
            Trace("inst-gen-debug") << "Choose selection literal " << gn << std::endl;
            Trace("inst-gen-debug") << "  flags: " << isConst << " " << selectLitConstraints << " " << selectLitScore << std::endl;
            d_quant_selection_lit[f] = value ? n : n.notNode();
            selectionLitTerms.clear();
            selectionLitTerms.insert( selectionLitTerms.begin(), uf_terms.begin(), uf_terms.end() );
            if( !selectLitConstraints ){
              break;
            }
          }
          pref = 1;
        }else{
          pref = -1;
        }
        //if we are not yet SAT, so we will add to preferences
        if( d_qe->getModel()->isQuantifierActive( f ) ){
          Debug("fmf-model-prefs") << "  It is " << ( pref==1 ? "pro" : "con" );
          Debug("fmf-model-prefs") << " the definition of " << n << std::endl;
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            pro_con[ pref==1 ? 0 : 1 ].push_back( uf_terms[j] );
          }
        }
      }
    }
    //process information about selection literal for f
    if( !d_quant_selection_lit[f].isNull() ){
      d_quant_selection_lit_terms[f].insert( d_quant_selection_lit_terms[f].begin(), selectionLitTerms.begin(), selectionLitTerms.end() );
      for( int i=0; i<(int)selectionLitTerms.size(); i++ ){
        d_term_selection_lit[ selectionLitTerms[i] ] = d_quant_selection_lit[f];
        d_op_selection_terms[ selectionLitTerms[i].getOperator() ].push_back( selectionLitTerms[i] );
      }
    }else{
      Trace("inst-gen-warn") << "WARNING: " << f << " has no selection literals" << std::endl;
    }
    //process information about requirements and preferences of quantifier f
    if( !d_qe->getModel()->isQuantifierActive( f ) ){
      Debug("fmf-model-prefs") << "  * Constant SAT due to definition of ops: ";
      for( int i=0; i<(int)selectionLitTerms.size(); i++ ){
        Debug("fmf-model-prefs") << selectionLitTerms[i] << " ";
        d_uf_prefs[ selectionLitTerms[i].getOperator() ].d_reconsiderModel = false;
      }
      Debug("fmf-model-prefs") << std::endl;
    }else{
      //note quantifier's value preferences to models
      for( int k=0; k<2; k++ ){
        for( int j=0; j<(int)pro_con[k].size(); j++ ){
          Node op = pro_con[k][j].getOperator();
          Node r = fmig->getRepresentative( pro_con[k][j] );
          d_uf_prefs[op].setValuePreference( f, pro_con[k][j], r, k==0 );
        }
      }
    }
  }
}

int QModelBuilderDefault::doInstGen( FirstOrderModel* fm, Node f ){
  int addedLemmas = 0;
  //we wish to add all known exceptions to our selection literal for f. this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  if( !d_quant_selection_lit[f].isNull() ){
    Trace("inst-gen") << "Do Inst-Gen for " << f << std::endl;
    for( size_t i=0; i<d_quant_selection_lit_candidates[f].size(); i++ ){
      bool phase = d_quant_selection_lit_candidates[f][i].getKind()!=NOT;
      Node lit = d_quant_selection_lit_candidates[f][i].getKind()==NOT ? d_quant_selection_lit_candidates[f][i][0] : d_quant_selection_lit_candidates[f][i];
      Assert( TermDb::hasInstConstAttr(lit) );
      std::vector< Node > tr_terms;
      if( lit.getKind()==APPLY_UF ){
        //only match predicates that are contrary to this one, use literal matching
        Node eq = NodeManager::currentNM()->mkNode( EQUAL, lit, !phase ? fm->d_true : fm->d_false );
        tr_terms.push_back( eq );
      }else if( lit.getKind()==EQUAL ){
        //collect trigger terms
        for( int j=0; j<2; j++ ){
          if( TermDb::hasInstConstAttr(lit[j]) ){
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
        inst::Trigger* tr = inst::Trigger::mkTrigger( d_qe, f, tr_terms, true, inst::Trigger::TR_MAKE_NEW );
        //Notice() << "Trigger = " << (*tr) << std::endl;
        tr->resetInstantiationRound();
        tr->reset( Node::null() );
        //d_qe->d_optInstMakeRepresentative = false;
        //d_qe->d_optMatchIgnoreModelBasis = true;
        addedLemmas += tr->addInstantiations( d_quant_basis_match[f] );
      }
    }
  }
  return addedLemmas;
}

void QModelBuilderDefault::constructModelUf( FirstOrderModel* fm, Node op ){
  FirstOrderModelIG* fmig = fm->asFirstOrderModelIG();
  if( optReconsiderFuncConstants() ){
    //reconsider constant functions that weren't necessary
    if( d_uf_model_constructed[op] ){
      if( d_uf_prefs[op].d_reconsiderModel ){
        //if we are allowed to reconsider default value, then see if the default value can be improved
        Node v = d_uf_prefs[op].d_const_val;
        if( d_uf_prefs[op].d_value_pro_con[0][v].empty() ){
          Debug("fmf-model-cons-debug") << "Consider changing the default value for " << op << std::endl;
          fmig->d_uf_model_tree[op].clear();
          fmig->d_uf_model_gen[op].clear();
          d_uf_model_constructed[op] = false;
        }
      }
    }
  }
  if( !d_uf_model_constructed[op] ){
    //construct the model for the uninterpretted function/predicate
    bool setDefaultVal = true;
    Node defaultTerm = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
    Trace("fmf-model-cons") << "Construct model for " << op << "..." << std::endl;
    //set the values in the model
    for( size_t i=0; i<fmig->d_uf_terms[op].size(); i++ ){
      Node n = fmig->d_uf_terms[op][i];
      if( isTermActive( n ) ){
        Node v = fmig->getRepresentative( n );
        Trace("fmf-model-cons") << "Set term " << n << " : " << fmig->d_rep_set.getIndexFor( v ) << " " << v << std::endl;
        //if this assertion did not help the model, just consider it ground
        //set n = v in the model tree
        //set it as ground value
        fmig->d_uf_model_gen[op].setValue( fm, n, v );
        if( fmig->d_uf_model_gen[op].optUsePartialDefaults() ){
          //also set as default value if necessary
          if( n.hasAttribute(ModelBasisArgAttribute()) && n.getAttribute(ModelBasisArgAttribute())!=0 ){
            Trace("fmf-model-cons") << "  Set as default." << std::endl;
            fmig->d_uf_model_gen[op].setValue( fm, n, v, false );
            if( n==defaultTerm ){
              //incidentally already set, we will not need to find a default value
              setDefaultVal = false;
            }
          }
        }else{
          if( n==defaultTerm ){
            fmig->d_uf_model_gen[op].setValue( fm, n, v, false );
            //incidentally already set, we will not need to find a default value
            setDefaultVal = false;
          }
        }
      }
    }
    //set the overall default value if not set already  (is this necessary??)
    if( setDefaultVal ){
      Trace("fmf-model-cons") << "  Choose default value..." << std::endl;
      //chose defaultVal based on heuristic, currently the best ratio of "pro" responses
      Node defaultVal = d_uf_prefs[op].getBestDefaultValue( defaultTerm, fm );
      if( defaultVal.isNull() ){
        if (!fmig->d_rep_set.hasType(defaultTerm.getType())) {
          Node mbt = d_qe->getTermDatabase()->getModelBasisTerm(defaultTerm.getType());
          fmig->d_rep_set.d_type_reps[defaultTerm.getType()].push_back(mbt);
        }
        defaultVal = fmig->d_rep_set.d_type_reps[defaultTerm.getType()][0];
      }
      Assert( !defaultVal.isNull() );
      Trace("fmf-model-cons") << "Set default term : " << fmig->d_rep_set.getIndexFor( defaultVal ) << std::endl;
      fmig->d_uf_model_gen[op].setValue( fm, defaultTerm, defaultVal, false );
    }
    Debug("fmf-model-cons") << "  Making model...";
    fmig->d_uf_model_gen[op].makeModel( fm, fmig->d_uf_model_tree[op] );
    d_uf_model_constructed[op] = true;
    Debug("fmf-model-cons") << "  Finished constructing model for " << op << "." << std::endl;
  }
}

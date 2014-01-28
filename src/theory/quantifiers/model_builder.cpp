/*********************                                                        */
/*! \file model_builder.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: none
 ** Minor contributors (to current version): Kshitij Bansal, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of model builder class
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/inst_gen.h"
#include "theory/quantifiers/trigger.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;


QModelBuilder::QModelBuilder( context::Context* c, QuantifiersEngine* qe ) :
TheoryEngineModelBuilder( qe->getTheoryEngine() ), d_curr_model( c, NULL ), d_qe( qe ){
  d_considerAxioms = true;
}

bool QModelBuilder::isQuantifierActive( Node f ) {
  return !f.hasAttribute(QRewriteRuleAttribute());
}


bool QModelBuilder::optUseModel() {
  return options::mbqiMode()!=MBQI_NONE || options::fmfBoundInt();
}

void QModelBuilder::debugModel( FirstOrderModel* fm ){
  //debug the model: cycle through all instantiations for all quantifiers, report ones that are not true
  if( Trace.isOn("quant-model-warn") ){
    Trace("quant-model-warn") << "Testing quantifier instantiations..." << std::endl;
    int tests = 0;
    int bad = 0;
    for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
      Node f = fm->getAssertedQuantifier( i );
      std::vector< Node > vars;
      for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
        vars.push_back( f[0][j] );
      }
      RepSetIterator riter( d_qe, &(fm->d_rep_set) );
      if( riter.setQuantifier( f ) ){
        while( !riter.isFinished() ){
          tests++;
          std::vector< Node > terms;
          for( int i=0; i<riter.getNumTerms(); i++ ){
            terms.push_back( riter.getTerm( i ) );
          }
          Node n = d_qe->getInstantiation( f, vars, terms );
          Node val = fm->getValue( n );
          if( val!=fm->d_true ){
            Trace("quant-model-warn") << "*******  Instantiation " << n << " for " << std::endl;
            Trace("quant-model-warn") << "         " << f << std::endl;
            Trace("quant-model-warn") << "         Evaluates to " << val << std::endl;
            bad++;
          }
          riter.increment();
        }
        Trace("quant-model-warn") << "Tested " << tests << " instantiations";
        if( bad>0 ){
          Trace("quant-model-warn") << ", " << bad << " failed" << std::endl;
        }
        Trace("quant-model-warn") << "." << std::endl;
      }else{
        Trace("quant-model-warn") << "Warning: Could not test quantifier " << f << std::endl;
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
QModelBuilder( c, qe ) {

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
      for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
        Node f = fm->getAssertedQuantifier( i );
        if( isQuantifierActive( f ) ){
          int lems = initializeQuantifier( f, f );
          d_statistics.d_init_inst_gen_lemmas += lems;
          d_addedLemmas += lems;
        }
      }
      if( d_addedLemmas>0 ){
        Trace("model-engine") << "Initialize, Added Lemmas = " << d_addedLemmas << std::endl;
      }else{
        //initialize model
        fm->initialize( d_considerAxioms );
        //analyze the functions
        Trace("model-engine-debug") << "Analyzing model..." << std::endl;
        analyzeModel( fm );
        //analyze the quantifiers
        Trace("model-engine-debug") << "Analyzing quantifiers..." << std::endl;
        d_quant_sat.clear();
        d_uf_prefs.clear();
        for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
          Node f = fm->getAssertedQuantifier( i );
          if( isQuantifierActive( f ) ){
            analyzeQuantifier( fm, f );
          }
        }

        //if applicable, find exceptions to model via inst-gen
        if( optInstGen() ){
          d_didInstGen = true;
          d_instGenMatches = 0;
          d_numQuantSat = 0;
          d_numQuantInstGen = 0;
          d_numQuantNoInstGen = 0;
          d_numQuantNoSelForm = 0;
          //now, see if we know that any exceptions via InstGen exist
          Trace("model-engine-debug") << "Perform InstGen techniques for quantifiers..." << std::endl;
          for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
            Node f = fm->getAssertedQuantifier( i );
            if( isQuantifierActive( f ) ){
              int lems = doInstGen( fm, f );
              d_statistics.d_inst_gen_lemmas += lems;
              d_addedLemmas += lems;
              //temporary
              if( lems>0 ){
                d_numQuantInstGen++;
              }else if( d_quant_sat.find( f )!=d_quant_sat.end() ){
                d_numQuantSat++;
              }else if( hasInstGen( f ) ){
                d_numQuantNoInstGen++;
              }else{
                d_numQuantNoSelForm++;
              }
              if( optOneQuantPerRoundInstGen() && lems>0 ){
                break;
              }
            }else if( d_quant_sat.find( f )!=d_quant_sat.end() ){
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
          /*
          //build model for arrays
          for( std::map< Node, arrays::ArrayModel >::iterator it = fm->d_array_model.begin(); it != fm->d_array_model.end(); ++it ){
            //consult the model basis select term
            // i.e. the default value for array A is the value of select( A, e ), where e is the model basis term
            TypeNode tn = it->first.getType();
            Node selModelBasis = NodeManager::currentNM()->mkNode( SELECT, it->first, fm->getTermDatabase()->getModelBasisTerm( tn[0] ) );
            it->second.setDefaultValue( fm->getRepresentative( selModelBasis ) );
          }
          */
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
    if( d_qe->addInstantiation( fp, d_quant_basis_match[f], false ) ){
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
      if( !n.getAttribute(NoMatchAttribute()) ){
        Node v = fmig->getRepresentative( n );
        if( i==0 ){
          d_uf_prefs[op].d_const_val = v;
        }else if( v!=d_uf_prefs[op].d_const_val ){
          d_uf_prefs[op].d_const_val = Node::null();
          break;
        }
      }
      //for calculating terms that we don't need to consider
      if( !n.getAttribute(NoMatchAttribute()) || n.getAttribute(ModelBasisArgAttribute())!=0 ){
        if( !n.getAttribute(BasisNoMatchAttribute()) ){
          //need to consider if it is not congruent modulo model basis
          if( !tabt.addTerm( fmig, n ) ){
             BasisNoMatchAttribute bnma;
             n.setAttribute(bnma,true);
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

bool QModelBuilderIG::optInstGen(){
  return options::fmfInstGen();
}

bool QModelBuilderIG::optOneQuantPerRoundInstGen(){
  return options::fmfInstGenOneQuantPerRound();
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
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_partial_quants_init);
  StatisticsRegistry::registerStat(&d_init_inst_gen_lemmas);
  StatisticsRegistry::registerStat(&d_inst_gen_lemmas);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_eval_lits);
  StatisticsRegistry::registerStat(&d_eval_lits_unknown);
}

QModelBuilderIG::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_partial_quants_init);
  StatisticsRegistry::unregisterStat(&d_init_inst_gen_lemmas);
  StatisticsRegistry::unregisterStat(&d_inst_gen_lemmas);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_eval_lits);
  StatisticsRegistry::unregisterStat(&d_eval_lits_unknown);
}

bool QModelBuilderIG::isQuantifierActive( Node f ){
  return !f.hasAttribute(QRewriteRuleAttribute()) &&
         ( d_considerAxioms || !f.getAttribute(AxiomAttribute()) ) && d_quant_sat.find( f )==d_quant_sat.end();
}

bool QModelBuilderIG::isTermActive( Node n ){
  return !n.getAttribute(NoMatchAttribute()) || //it is not congruent to another active term
         ( n.getAttribute(ModelBasisArgAttribute())!=0 && !n.getAttribute(BasisNoMatchAttribute()) ); //or it has model basis arguments
                                                                                                      //and is not congruent modulo model basis
                                                                                                      //to another active term
}


//do exhaustive instantiation
bool QModelBuilderIG::doExhaustiveInstantiation( FirstOrderModel * fm, Node f, int effort ) {
  if( optUseModel() ){
    RepSetIterator riter( d_qe, &(d_qe->getModel()->d_rep_set) );
    if( riter.setQuantifier( f ) ){
      FirstOrderModelIG * fmig = (FirstOrderModelIG*)d_qe->getModel();
      Debug("inst-fmf-ei") << "Reset evaluate..." << std::endl;
      fmig->resetEvaluate();
      Debug("inst-fmf-ei") << "Begin instantiation..." << std::endl;
      while( !riter.isFinished() && ( d_addedLemmas==0 || !options::fmfOneInstPerRound() ) ){
        d_triedLemmas++;
        for( int i=0; i<(int)riter.d_index.size(); i++ ){
          Trace("try") << i << " : " << riter.d_index[i] << " : " << riter.getTerm( i ) << std::endl;
        }
        int eval = 0;
        int depIndex;
        //see if instantiation is already true in current model
        Debug("fmf-model-eval") << "Evaluating ";
        riter.debugPrintSmall("fmf-model-eval");
        Debug("fmf-model-eval") << "Done calculating terms." << std::endl;
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
            m.set( d_qe, riter.d_index_order[i], riter.getTerm( i ) );
          }
          Debug("fmf-model-eval") << "* Add instantiation " << m << std::endl;
          //add as instantiation
          if( d_qe->addInstantiation( f, m ) ){
            d_addedLemmas++;
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
    d_incomplete_check = riter.d_incomplete;
    return true;
  }else{
    return false;
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
  int selectLitScore = -1;
  QuantPhaseReq* qpr = d_qe->getPhaseRequirements( f );
  for( std::map< Node, bool >::iterator it = qpr->d_phase_reqs.begin(); it != qpr->d_phase_reqs.end(); ++it ){
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
          selectLit = selectLit || d_quant_sat.find( f )==d_quant_sat.end();
          d_quant_sat[f] = true;
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
      if( d_quant_sat.find( f )==d_quant_sat.end() ){
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
  if( d_quant_sat.find( f )!=d_quant_sat.end() ){
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
        Node eq = NodeManager::currentNM()->mkNode( IFF, lit, !phase ? fm->d_true : fm->d_false );
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
        inst::Trigger* tr = inst::Trigger::mkTrigger( d_qe, f, tr_terms, 0, true, inst::Trigger::TR_MAKE_NEW, options::smartTriggers() );
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




//////////////////////  Inst-Gen style Model Builder ///////////

void QModelBuilderInstGen::reset( FirstOrderModel* fm ){
  //for new inst gen
  d_quant_selection_formula.clear();
  d_term_selected.clear();

  //d_sub_quant_inst_trie.clear();//*
}

int QModelBuilderInstGen::initializeQuantifier( Node f, Node fp ){
  int addedLemmas = QModelBuilderIG::initializeQuantifier( f, fp );
  for( size_t i=0; i<d_sub_quants[f].size(); i++ ){
    addedLemmas += initializeQuantifier( d_sub_quants[f][i], fp );
  }
  return addedLemmas;
}

void QModelBuilderInstGen::analyzeQuantifier( FirstOrderModel* fm, Node f ){
  //Node fp = getParentQuantifier( f );//*
  //bool quantRedundant = ( f!=fp && d_sub_quant_inst_trie[fp].addInstMatch( d_qe, fp, d_sub_quant_inst[ f ], true ) );
  //if( f==fp || d_sub_quant_inst_trie[fp].addInstMatch( d_qe, fp, d_sub_quant_inst[ f ], true ) ){//*
  Trace("sel-form-debug") << "* Analyze " << f << std::endl;
  //determine selection formula, set terms in selection formula as being selected
  Node s = getSelectionFormula( d_qe->getTermDatabase()->getInstConstantBody( f ),
                                d_qe->getTermDatabase()->getModelBasisBody( f ), true, 0 );
  //if( !s.isNull() ){
  //  s = Rewriter::rewrite( s );
  //}
  Trace("sel-form-debug") << "Selection formula " << f << std::endl;
  Trace("sel-form-debug") << "                  " << s << std::endl;
  if( !s.isNull() ){
    d_quant_selection_formula[f] = s;
    Node gs = d_qe->getTermDatabase()->getModelBasis( f, s );
    setSelectedTerms( gs );
    //quick check if it is constant sat
    if( hasConstantDefinition( s ) ){
      d_quant_sat[f] = true;
    }
  }else{
    Trace("sel-form-null") << "*** No selection formula for " << f << std::endl;
  }
  //analyze sub quantifiers
  if( d_quant_sat.find( f )==d_quant_sat.end() ){
    for( size_t i=0; i<d_sub_quants[f].size(); i++ ){
      analyzeQuantifier( fm, d_sub_quants[f][i] );
    }
  }
}


int QModelBuilderInstGen::doInstGen( FirstOrderModel* fm, Node f ){
  int addedLemmas = 0;
  if( d_quant_sat.find( f )==d_quant_sat.end() ){
    Node fp = d_sub_quant_parent.find( f )==d_sub_quant_parent.end() ? f : d_sub_quant_parent[f];
    if( fp!=f ) Trace("inst-gen") << "   ";
    Trace("inst-gen") << "Do Inst-Gen for " << f << std::endl;
    if( fp!=f ) Trace("inst-gen") << "   ";
    Trace("inst-gen") << "Sel Form :      " << d_quant_selection_formula[f] << std::endl;
    //we wish to add all known exceptions to our selection formula for f. this will help to refine our current model.
    if( !d_quant_selection_formula[f].isNull() ){
      //first, try on sub quantifiers
      bool subQuantSat = true;
      for( size_t i=0; i<d_sub_quants[f].size(); i++ ){
        addedLemmas += doInstGen( fm, d_sub_quants[f][i] );
        if( d_quant_sat.find( d_sub_quants[f][i] )==d_quant_sat.end() ){
          subQuantSat = false;
        }
      }
      if( addedLemmas>0 || !subQuantSat ){
        Trace("inst-gen") << " -> children added lemmas or non-satisfied" << std::endl;
        return addedLemmas;
      }else{
        Trace("inst-gen-debug") << "Calculate inst-gen instantiations..." << std::endl;
        //get all possible values of selection formula
        InstGenProcess igp( d_quant_selection_formula[f] );
        std::vector< Node > considered;
        considered.push_back( fm->d_false );
        igp.calculateMatches( d_qe, f, considered, true );
        //igp.calculateMatches( d_qe, f);
        Trace("inst-gen-debug") << "Add inst-gen instantiations (" << igp.getNumMatches() << ")..." << std::endl;
        for( int i=0; i<igp.getNumMatches(); i++ ){
          //if the match is not already true in the model
          if( igp.getMatchValue( i )!=fm->d_true ){
            InstMatch m( f );
            igp.getMatch( d_qe->getEqualityQuery(), i, m );
            //Trace("inst-gen-debug") << "Inst Gen : " << m << std::endl;
            //we only consider matches that are non-empty
            //  matches that are empty should trigger other instances that are non-empty
            if( !m.empty() ){
              Trace("inst-gen-debug") << "Get in terms of parent..." << std::endl;
              //translate to be in terms match in terms of fp
              InstMatch mp(f);
              getParentQuantifierMatch( mp, fp, m, f );
              //if this is a partial instantion
              if( !m.isComplete() ){
                //need to make it internal here
                //Trace("mkInternal") << "Make internal representative " << mp << std::endl;
                //mp.makeInternalRepresentative( d_qe );
                //Trace("mkInternal") << "Got " << mp << std::endl;
                //if the instantiation does not yet exist
                if( d_sub_quant_inst_trie[fp].addInstMatch( d_qe, fp, mp, true ) ){
                  //also add it to children
                  d_child_sub_quant_inst_trie[f].addInstMatch( d_qe, f, m );
                  //get the partial instantiation pf
                  Node pf = d_qe->getInstantiation( fp, mp );
                  Trace("inst-gen-pi") << "Partial instantiation of " << f << std::endl;
                  Trace("inst-gen-pi") << "                         " << pf << std::endl;
                  d_sub_quants[ f ].push_back( pf );
                  d_sub_quant_inst[ pf ] = InstMatch( &mp );
                  d_sub_quant_parent[ pf ] = fp;
                  //now make mp a complete match
                  mp.add( d_quant_basis_match[ fp ] );
                  d_quant_basis_match[ pf ] = InstMatch( &mp );
                  ++(d_statistics.d_num_quants_init);
                  ++(d_statistics.d_num_partial_quants_init);
                  addedLemmas += initializeQuantifier( pf, fp );
                  Trace("inst-gen-pi") << "Done adding partial instantiation" << std::endl;
                  subQuantSat = false;
                }
              }else{
                if( d_qe->addInstantiation( fp, mp ) ){
                  addedLemmas++;
                }
              }
            }
          }
        }
        if( addedLemmas==0 ){
          //all sub quantifiers must be satisfied as well
          if( subQuantSat ){
            d_quant_sat[ f ] = true;
          }
        }
        if( fp!=f ) Trace("inst-gen") << "   ";
        Trace("inst-gen") << "  -> added lemmas = " << addedLemmas << std::endl;
        if( d_quant_sat.find( f )!=d_quant_sat.end() ){
          if( fp!=f ) Trace("inst-gen") << "   ";
          Trace("inst-gen") << "  -> *** it is satisfied" << std::endl;
        }
      }
    }
  }
  return addedLemmas;
}

Node mkAndSelectionFormula( std::vector< Node >& children ){
  std::vector< Node > ch;
  for( size_t i=0; i<children.size(); i++ ){
    if( children[i].getKind()==AND ){
      for( size_t j=0; j<children[i].getNumChildren(); j++ ){
        ch.push_back( children[i][j] );
      }
    }else{
      ch.push_back( children[i] );
    }
  }
  return NodeManager::currentNM()->mkNode( AND, ch );
}
Node mkAndSelectionFormula( Node n1, Node n2 ){
  std::vector< Node > children;
  children.push_back( n1 );
  children.push_back( n2 );
  return mkAndSelectionFormula( children );
}

//if possible, returns a formula n' such that n' => ( n <=> polarity ), and n' is true in the current context,
//   and NULL otherwise
Node QModelBuilderInstGen::getSelectionFormula( Node fn, Node n, bool polarity, int useOption ){
  Trace("sel-form-debug") << "Looking for selection formula " << n << " " << polarity << std::endl;
  Node ret;
  if( n.getKind()==NOT ){
    ret = getSelectionFormula( fn[0], n[0], !polarity, useOption );
  }else if( n.getKind()==OR || n.getKind()==AND ){
    //whether we only need to find one or all
    bool favorPol = ( n.getKind()!=AND && polarity ) || ( n.getKind()==AND && !polarity );
    std::vector< Node > children;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node fnc = fn[i];
      Node nc = n[i];
      Node nn = getSelectionFormula( fnc, nc, polarity, useOption );
      if( nn.isNull() && !favorPol ){
        //cannot make selection formula
        children.clear();
        break;
      }
      if( !nn.isNull() ){
        //if( favorPol ){   //temporary
        //  return nn;      //
        //}                 //
        if( std::find( children.begin(), children.end(), nn )==children.end() ){
          children.push_back( nn );
        }
      }
    }
    if( !children.empty() ){
      if( favorPol ){
        //filter which formulas we wish to keep, make disjunction
        Node min_lit;
        int min_score = -1;
        for( size_t i=0; i<children.size(); i++ ){
          //if it is constant apply uf application, return it for sure
          if( hasConstantDefinition( children[i] ) ){
            min_lit = children[i];
            break;
          }else{
            int score = getSelectionFormulaScore( children[i] );
            if( min_score<0 || score<min_score ){
              min_score = score;
              min_lit = children[i];
            }
          }
        }
        //currently just return the best single literal
        ret = min_lit;
      }else{
        //selection formula must be conjunction of children
        ret = mkAndSelectionFormula( children );
      }
    }else{
      ret = Node::null();
    }
  }else if( n.getKind()==ITE ){
    Node nn;
    Node nc[2];
    //get selection formula for the
    for( int i=0; i<2; i++ ){
      nn = getSelectionFormula( fn[0], n[0], i==0, useOption );
      nc[i] = getSelectionFormula( fn[i+1], n[i+1], polarity, useOption );
      if( !nn.isNull() && !nc[i].isNull() ){
        ret = mkAndSelectionFormula( nn, nc[i] );
        break;
      }
    }
    if( ret.isNull() && !nc[0].isNull() && !nc[1].isNull() ){
      ret = mkAndSelectionFormula( nc[0], nc[1] );
    }
  }else if( n.getKind()==IFF ){
    bool opPol = !polarity;
    for( int p=0; p<2; p++ ){
      Node nn[2];
      for( int i=0; i<2; i++ ){
        bool pol = i==0 ? p==0 : ( opPol ? p!=0 : p==0 );
        nn[i] = getSelectionFormula( fn[i], n[i], pol, useOption );
        if( nn[i].isNull() ){
          break;
        }
      }
      if( !nn[0].isNull() && !nn[1].isNull() ){
        ret = mkAndSelectionFormula( nn[0], nn[1] );
      }
    }
  }else{
    //literal case
    //first, check if it is a usable selection literal
    if( isUsableSelectionLiteral( n, useOption ) ){
      bool value;
      if( d_qe->getValuation().hasSatValue( n, value ) ){
        if( value==polarity ){
          ret = fn;
          if( !polarity ){
            ret = ret.negate();
          }
        }else{
          Trace("sel-form-debug") << "  (wrong polarity)" << std::endl;
        }
      }else{
        Trace("sel-form-debug") << "  (does not have sat value)" << std::endl;
      }
    }else{
      Trace("sel-form-debug") << "  (is not usable literal)" << std::endl;
    }
  }
  Trace("sel-form-debug") << "   return " << ret << std::endl;
  return ret;
}

int QModelBuilderInstGen::getSelectionFormulaScore( Node fn ){
  if( fn.getType().isBoolean() ){
    if( fn.getKind()==APPLY_UF ){
      Node op = fn.getOperator();
      //return total number of terms
      return d_qe->getTermDatabase()->d_op_count[op];
    }else{
      int score = 0;
      for( size_t i=0; i<fn.getNumChildren(); i++ ){
        score += getSelectionFormulaScore( fn[i] );
      }
      return score;
    }
  }else{
    return 0;
  }
}

void QModelBuilderInstGen::setSelectedTerms( Node s ){

  //if it is apply uf and has model basis arguments, then mark term as being "selected"
  if( s.getKind()==APPLY_UF ){
    Assert( s.hasAttribute(ModelBasisArgAttribute()) );
    if( !s.hasAttribute(ModelBasisArgAttribute()) ) std::cout << "no mba!! " << s << std::endl;
    if( s.getAttribute(ModelBasisArgAttribute())!=0 ){
      d_term_selected[ s ] = true;
      Trace("sel-form-term") << "  " << s << " is a selected term." << std::endl;
    }
  }
  for( int i=0; i<(int)s.getNumChildren(); i++ ){
    setSelectedTerms( s[i] );
  }
}

bool QModelBuilderInstGen::isUsableSelectionLiteral( Node n, int useOption ){
  if( n.getKind()==FORALL ){
    return false;
  }else if( n.getKind()!=APPLY_UF ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //if it is a variable, then return false
      if( n[i].getAttribute(ModelBasisAttribute()) ){
        return false;
      }
    }
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    if( !isUsableSelectionLiteral( n[i], useOption ) ){
      return false;
    }
  }
  return true;
}

void QModelBuilderInstGen::getParentQuantifierMatch( InstMatch& mp, Node fp, InstMatch& m, Node f ){
  if( f!=fp ){
    //std::cout << "gpqm " << fp << " " << f << " " << m << std::endl;
    //std::cout << "     " << fp[0].getNumChildren() << " " << f[0].getNumChildren() << std::endl;
    int counter = 0;
    for( size_t i=0; i<fp[0].getNumChildren(); i++ ){
      if( (int)counter< (int)f[0].getNumChildren() ){
        if( fp[0][i]==f[0][counter] ){
          Node n = m.get( counter );
          if( !n.isNull() ){
            mp.set( d_qe, i, n );
          }
          counter++;
        }
      }
    }
    mp.add( d_sub_quant_inst[f] );
  }else{
    mp.add( m );
  }
}

void QModelBuilderInstGen::constructModelUf( FirstOrderModel* fm, Node op ){
  FirstOrderModelIG* fmig = fm->asFirstOrderModelIG();
  bool setDefaultVal = true;
  Node defaultTerm = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
  //set the values in the model
  for( size_t i=0; i<fmig->d_uf_terms[op].size(); i++ ){
    Node n = fmig->d_uf_terms[op][i];
    if( isTermActive( n ) ){
      Node v = fmig->getRepresentative( n );
      fmig->d_uf_model_gen[op].setValue( fm, n, v );
    }
    //also possible set as default
    if( d_term_selected.find( n )!=d_term_selected.end() || n==defaultTerm ){
      Node v = fmig->getRepresentative( n );
      fmig->d_uf_model_gen[op].setValue( fm, n, v, false );
      if( n==defaultTerm ){
        setDefaultVal = false;
      }
    }
  }
  //set the overall default value if not set already  (is this necessary??)
  if( setDefaultVal ){
    Node defaultVal = d_uf_prefs[op].getBestDefaultValue( defaultTerm, fm );
    fmig->d_uf_model_gen[op].setValue( fm, defaultTerm, defaultVal, false );
  }
  fmig->d_uf_model_gen[op].makeModel( fm, fmig->d_uf_model_tree[op] );
  d_uf_model_constructed[op] = true;
}

bool QModelBuilderInstGen::existsInstantiation( Node f, InstMatch& m, bool modEq, bool modInst ){
  return d_child_sub_quant_inst_trie[f].existsInstMatch( d_qe, f, m, modEq, true );
}

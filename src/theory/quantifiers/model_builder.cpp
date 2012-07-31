/*********************                                                        */
/*! \file model_builder.cpp
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
 ** \brief Implementation of model builder class
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_model.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/model_builder.h"

//#define ME_PRINT_WARNINGS

#define RECONSIDER_FUNC_CONSTANT
//#define ONE_QUANT_PER_ROUND_INST_GEN

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

ModelEngineBuilder::ModelEngineBuilder( QuantifiersEngine* qe ) :
TheoryEngineModelBuilder( qe->getTheoryEngine() ),
d_qe( qe ){

}

Node ModelEngineBuilder::chooseRepresentative( TheoryModel* m, Node eqc ){
  Assert( m->d_equalityEngine.hasTerm( eqc ) );
  Assert( m->d_equalityEngine.getRepresentative( eqc )==eqc );
  //avoid interpreted symbols
  if( isBadRepresentative( eqc ) ){
    eq::EqClassIterator eqc_i = eq::EqClassIterator( eqc, &m->d_equalityEngine );
    while( !eqc_i.isFinished() ){
      if( !isBadRepresentative( *eqc_i ) ){
        return *eqc_i;
      }
      ++eqc_i;
    }
    //otherwise, make new value?
    //Message() << "Warning: Bad rep " << eqc << std::endl;
  }
  return eqc;
}

bool ModelEngineBuilder::isBadRepresentative( Node n ){
  return n.getKind()==SELECT || n.getKind()==APPLY_SELECTOR;
}

void ModelEngineBuilder::processBuildModel( TheoryModel* m ) {
  d_addedLemmas = 0;
  //only construct first order model if optUseModel() is true
  if( optUseModel() ){
    FirstOrderModel* fm = (FirstOrderModel*)m;
    //initialize model
    fm->initialize();
    //analyze the functions
    analyzeModel( fm );
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
      if( Trace.isOn("model-engine") ){
        if( d_addedLemmas>0 ){
          Trace("model-engine") << "InstGen, added lemmas = " << d_addedLemmas << std::endl;
        }else{
          Trace("model-engine") << "No InstGen lemmas..." << std::endl;
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

void ModelEngineBuilder::analyzeModel( FirstOrderModel* fm ){
  //determine if any functions are constant
  for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
    Node op = it->first;
    for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
      Node n = fm->d_uf_terms[op][i];
      if( !n.getAttribute(NoMatchAttribute()) ){
        Node v = fm->getRepresentative( n );
        if( i==0 ){
          d_uf_prefs[op].d_const_val = v;
        }else if( v!=d_uf_prefs[op].d_const_val ){
          d_uf_prefs[op].d_const_val = Node::null();
          break;
        }
      }
    }
    if( !d_uf_prefs[op].d_const_val.isNull() ){
      fm->d_uf_model_gen[op].setDefaultValue( d_uf_prefs[op].d_const_val );
      fm->d_uf_model_gen[op].makeModel( fm, it->second );
      Debug("fmf-model-cons") << "Function " << op << " is the constant function ";
      fm->printRepresentativeDebug( "fmf-model-cons", d_uf_prefs[op].d_const_val );
      Debug("fmf-model-cons") << std::endl;
      d_uf_model_constructed[op] = true;
    }else{
      d_uf_model_constructed[op] = false;
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
          isConst = !d_uf_prefs[gn.getOperator()].d_const_val.isNull();
        }else if( gn.getKind()==EQUAL ){
          isConst = true;
          for( int j=0; j<2; j++ ){
            if( n[j].hasAttribute(InstConstantAttribute()) ){
              if( n[j].getKind()==APPLY_UF ){
                Node op = gn[j].getOperator();
                if( fm->d_uf_model_tree.find( op )!=fm->d_uf_model_tree.end() ){
                  uf_terms.push_back( gn[j] );
                  isConst = isConst && !d_uf_prefs[op].d_const_val.isNull();
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
      inst::Trigger* tr = inst::Trigger::mkTrigger( d_qe, f, tr_terms );
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
  for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
    finishBuildModelUf( fm, it->first );
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
  Debug("fmf-model-debug") << "Done building models." << std::endl;
}

void ModelEngineBuilder::finishBuildModelUf( FirstOrderModel* fm, Node op ){
#ifdef RECONSIDER_FUNC_CONSTANT
  if( d_uf_model_constructed[op] ){
    if( d_uf_prefs[op].d_reconsiderModel ){
      //if we are allowed to reconsider default value, then see if the default value can be improved
      Node v = d_uf_prefs[op].d_const_val;
      if( d_uf_prefs[op].d_value_pro_con[0][v].empty() ){
        Debug("fmf-model-cons-debug") << "Consider changing the default value for " << op << std::endl;
        fm->d_uf_model_tree[op].clear();
        fm->d_uf_model_gen[op].clear();
        d_uf_model_constructed[op] = false;
      }
    }
  }
#endif
  if( !d_uf_model_constructed[op] ){
    //construct the model for the uninterpretted function/predicate
    bool setDefaultVal = true;
    Node defaultTerm = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
    Debug("fmf-model-cons") << "Construct model for " << op << "..." << std::endl;
    //set the values in the model
    for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
      Node n = fm->d_uf_terms[op][i];
      fm->getTermDatabase()->computeModelBasisArgAttribute( n );
      if( !n.getAttribute(NoMatchAttribute()) || n.getAttribute(ModelBasisArgAttribute())==1 ){
        Node v = fm->getRepresentative( n );
        //if this assertion did not help the model, just consider it ground
        //set n = v in the model tree
        Debug("fmf-model-cons") << "  Set " << n << " = ";
        fm->printRepresentativeDebug( "fmf-model-cons", v );
        Debug("fmf-model-cons") << std::endl;
        //set it as ground value
        fm->d_uf_model_gen[op].setValue( fm, n, v );
        if( fm->d_uf_model_gen[op].optUsePartialDefaults() ){
          //also set as default value if necessary
          //if( n.getAttribute(ModelBasisArgAttribute())==1 && !d_term_pro_con[0][n].empty() ){
          if( n.hasAttribute(ModelBasisArgAttribute()) && n.getAttribute(ModelBasisArgAttribute())==1 ){
            fm->d_uf_model_gen[op].setValue( fm, n, v, false );
            if( n==defaultTerm ){
              //incidentally already set, we will not need to find a default value
              setDefaultVal = false;
            }
          }
        }else{
          if( n==defaultTerm ){
            fm->d_uf_model_gen[op].setValue( fm, n, v, false );
            //incidentally already set, we will not need to find a default value
            setDefaultVal = false;
          }
        }
      }
    }
    //set the overall default value if not set already  (is this necessary??)
    if( setDefaultVal ){
      Debug("fmf-model-cons") << "  Choose default value..." << std::endl;
      //chose defaultVal based on heuristic, currently the best ratio of "pro" responses
      Node defaultVal = d_uf_prefs[op].getBestDefaultValue( defaultTerm, fm );
      Assert( !defaultVal.isNull() );
      fm->d_uf_model_gen[op].setValue( fm, defaultTerm, defaultVal, false );
    }
    Debug("fmf-model-cons") << "  Making model...";
    fm->d_uf_model_gen[op].makeModel( fm, fm->d_uf_model_tree[op] );
    d_uf_model_constructed[op] = true;
    Debug("fmf-model-cons") << "  Finished constructing model for " << op << "." << std::endl;
  }
}

void ModelEngineBuilder::finishProcessBuildModel( TheoryModel* m ){
  for( std::map< Node, Node >::iterator it = m->d_reps.begin(); it != m->d_reps.end(); ++it ){
    //build proper representatives (TODO)
  }
}

bool ModelEngineBuilder::optUseModel() {
  return options::fmfModelBasedInst();
}

bool ModelEngineBuilder::optInstGen(){
  return options::fmfInstGen();
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

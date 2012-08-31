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
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/model_builder.h"
#include "theory/quantifiers/quantifiers_attributes.h"

#define RECONSIDER_FUNC_CONSTANT

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

ModelEngineBuilder::ModelEngineBuilder( context::Context* c, QuantifiersEngine* qe ) :
TheoryEngineModelBuilder( qe->getTheoryEngine() ),
d_qe( qe ), d_curr_model( c, NULL ){
  d_considerAxioms = true;
}

Node ModelEngineBuilder::chooseRepresentative( TheoryModel* m, Node eqc, bool fullModel ){
  if( fullModel ){
    return TheoryEngineModelBuilder::chooseRepresentative( m, eqc, fullModel );
  }else{
    Assert( m->d_equalityEngine.hasTerm( eqc ) );
    Assert( m->d_equalityEngine.getRepresentative( eqc )==eqc );
    //avoid bad representatives
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
}

bool ModelEngineBuilder::isBadRepresentative( Node n ){
  //avoid interpreted symbols
  return n.getKind()==SELECT || n.getKind()==APPLY_SELECTOR;
}

void ModelEngineBuilder::processBuildModel( TheoryModel* m, bool fullModel ) {
  FirstOrderModel* fm = (FirstOrderModel*)m;
  if( fullModel ){
    Assert( d_curr_model==fm );
    //update models
    for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
      it->second.update( fm );
    }

  }else{
    d_curr_model = fm;
    //build model for relevant symbols contained in quantified formulas
    d_addedLemmas = 0;
    //only construct first order model if optUseModel() is true
    if( optUseModel() ){
      //initialize model
      fm->initialize( d_considerAxioms );
      //analyze the functions
      Trace("model-engine-debug") << "Analyzing model..." << std::endl;
      analyzeModel( fm );
      //analyze the quantifiers
      Trace("model-engine-debug") << "Analyzing quantifiers..." << std::endl;
      analyzeQuantifiers( fm );
      //if applicable, find exceptions
      if( optInstGen() ){
        //now, see if we know that any exceptions via InstGen exist
        Trace("model-engine-debug") << "Perform InstGen techniques for quantifiers..." << std::endl;
        for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
          Node f = fm->getAssertedQuantifier( i );
          if( isQuantifierActive( f ) ){
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
      }
      if( d_addedLemmas==0 ){
        //if no immediate exceptions, build the model
        //  this model will be an approximation that will need to be tested via exhaustive instantiation
        Trace("model-engine-debug") << "Building model..." << std::endl;
        constructModel( fm );
      }
    }
  }
}

void ModelEngineBuilder::analyzeModel( FirstOrderModel* fm ){
  d_uf_model_constructed.clear();
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
  d_quant_sat.clear();
  d_quant_selection_lit.clear();
  d_quant_selection_lit_candidates.clear();
  d_quant_selection_lit_terms.clear();
  d_term_selection_lit.clear();
  d_op_selection_terms.clear();
  d_uf_prefs.clear();
  int quantSatInit = 0;
  int nquantSatInit = 0;
  //analyze the preferences of each quantifier
  for( int i=0; i<(int)fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    if( isQuantifierActive( f ) ){
      Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
      //the pro/con preferences for this quantifier
      std::vector< Node > pro_con[2];
      //the terms in the selection literal we choose
      std::vector< Node > selectionLitTerms;
      //for each asserted quantifier f,
      // - determine selection literals
      // - check which function/predicates have good and bad definitions for satisfying f
      for( std::map< Node, bool >::iterator it = d_qe->d_phase_reqs[f].begin();
           it != d_qe->d_phase_reqs[f].end(); ++it ){
        //the literal n is phase-required for quantifier f
        Node n = it->first;
        Node gn = d_qe->getTermDatabase()->getModelBasis( n );
        Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
        bool value;
        //if the corresponding ground abstraction literal has a SAT value
        if( d_qe->getValuation().hasSatValue( gn, value ) ){
          //collect the non-ground uf terms that this literal contains
          //  and compute if all of the symbols in this literal have
          //  constant definitions.
          bool isConst = true;
          std::vector< Node > uf_terms;
          if( n.hasAttribute(InstConstantAttribute()) ){
            isConst = false;
            if( gn.getKind()==APPLY_UF ){
              uf_terms.push_back( gn );
              isConst = !d_uf_prefs[gn.getOperator()].d_const_val.isNull();
            }else if( gn.getKind()==EQUAL ){
              isConst = true;
              for( int j=0; j<2; j++ ){
                if( n[j].hasAttribute(InstConstantAttribute()) ){
                  if( n[j].getKind()==APPLY_UF &&
                      fm->d_uf_model_tree.find( gn[j].getOperator() )!=fm->d_uf_model_tree.end() ){
                    uf_terms.push_back( gn[j] );
                    isConst = isConst && !d_uf_prefs[ gn[j].getOperator() ].d_const_val.isNull();
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
            //see if we wish to choose this as a selection literal
            d_quant_selection_lit_candidates[f].push_back( value ? n : n.notNode() );
            if( selectLit ){
              Trace("inst-gen-debug") << "Choose selection literal " << gn << std::endl;
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
        Trace("inst-gen-warn") << "WARNING: " << f << " has no selection literals (is the body of f clausified?)" << std::endl;
      }
      //process information about requirements and preferences of quantifier f
      if( d_quant_sat.find( f )!=d_quant_sat.end() ){
        Debug("fmf-model-prefs") << "  * Constant SAT due to definition of ops: ";
        for( int i=0; i<(int)selectionLitTerms.size(); i++ ){
          Debug("fmf-model-prefs") << selectionLitTerms[i] << " ";
          d_uf_prefs[ selectionLitTerms[i].getOperator() ].d_reconsiderModel = false;
        }
        Debug("fmf-model-prefs") << std::endl;
        quantSatInit++;
        ++(d_statistics.d_pre_sat_quant);
      }else{
        nquantSatInit++;
        ++(d_statistics.d_pre_nsat_quant);
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
  }
  Debug("fmf-model-prefs") << "Pre-Model Completion: Quantifiers SAT: " << quantSatInit << " / " << (quantSatInit+nquantSatInit) << std::endl;
}

int ModelEngineBuilder::doInstGen( FirstOrderModel* fm, Node f ){
  int addedLemmas = 0;
  //we wish to add all known exceptions to our selection literal for f. this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  if( !d_quant_selection_lit[f].isNull() ){
#if 0
    bool phase = d_quant_selection_lit[f].getKind()!=NOT;
    Node lit = d_quant_selection_lit[f].getKind()==NOT ? d_quant_selection_lit[f][0] : d_quant_selection_lit[f];
    Assert( lit.hasAttribute(InstConstantAttribute()) );
    for( size_t i=0; i<d_quant_selection_lit_terms[f].size(); i++ ){
      Node n1 = d_quant_selection_lit_terms[f][i];
      Node op = d_quant_selection_lit_terms[f][i].getOperator();
      //check all other selection literals involving "op"
      for( size_t i=0; i<d_op_selection_terms[op].size(); i++ ){
        Node n2 = d_op_selection_terms[op][i];
        Node n2_lit = d_term_selection_lit[ n2 ];
        if( n2_lit!=d_quant_selection_lit[f] ){
          //match n1 and n2
        }
      }
      if( addedLemmas==0 ){
        //check all ground terms involving "op"
        for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
          Node n2 = fm->d_uf_terms[op][i];
          if( n1!=n2 ){
            //match n1 and n2
          }
        }
      }
    }
#else
    Trace("inst-gen") << "Do Inst-Gen for " << f << std::endl;
    for( size_t i=0; i<d_quant_selection_lit_candidates[f].size(); i++ ){
      bool phase = d_quant_selection_lit_candidates[f][i].getKind()!=NOT;
      Node lit = d_quant_selection_lit_candidates[f][i].getKind()==NOT ? d_quant_selection_lit_candidates[f][i][0] : d_quant_selection_lit_candidates[f][i];
      Assert( lit.hasAttribute(InstConstantAttribute()) );
      std::vector< Node > tr_terms;
      if( lit.getKind()==APPLY_UF ){
        //only match predicates that are contrary to this one, use literal matching
        Node eq = NodeManager::currentNM()->mkNode( IFF, lit, !phase ? fm->d_true : fm->d_false );
        d_qe->getTermDatabase()->setInstantiationConstantAttr( eq, f );
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
#endif
  }
  return addedLemmas;
}

void ModelEngineBuilder::constructModel( FirstOrderModel* fm ){
  //build model for UF
  for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
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

void ModelEngineBuilder::constructModelUf( FirstOrderModel* fm, Node op ){
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
      d_qe->getTermDatabase()->computeModelBasisArgAttribute( n );
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

bool ModelEngineBuilder::optUseModel() {
  return options::fmfModelBasedInst();
}

bool ModelEngineBuilder::optInstGen(){
  return options::fmfInstGen();
}

bool ModelEngineBuilder::optOneQuantPerRoundInstGen(){
  return options::fmfInstGenOneQuantPerRound();
}

void ModelEngineBuilder::setEffort( int effort ){
  d_considerAxioms = effort>=1;
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

bool ModelEngineBuilder::isQuantifierActive( Node f ){
  return ( d_considerAxioms || !f.getAttribute(AxiomAttribute()) ) && d_quant_sat.find( f )==d_quant_sat.end();
}

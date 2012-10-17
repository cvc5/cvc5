/*********************                                                        */
/*! \file model_builder.cpp
 ** \verbatim
 ** Original author: ajreynol
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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
#include "theory/quantifiers/inst_gen.h"

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

void ModelEngineBuilder::processBuildModel( TheoryModel* m, bool fullModel ) {
  FirstOrderModel* fm = (FirstOrderModel*)m;
  if( fullModel ){
    Assert( d_curr_model==fm );
    //update models
    for( std::map< Node, uf::UfModelTree >::iterator it = fm->d_uf_model_tree.begin(); it != fm->d_uf_model_tree.end(); ++it ){
      it->second.update( fm );
      Trace("model-func") << "ModelEngineBuilder: Make function value from tree " << it->first << std::endl;
      //construct function values
      fm->d_uf_models[ it->first ] = it->second.getFunctionValue( "$x" );
    }
    TheoryEngineModelBuilder::processBuildModel( m, fullModel );
    //mark that the model has been set
    fm->markModelSet();
  }else{
    d_curr_model = fm;
    //build model for relevant symbols contained in quantified formulas
    d_addedLemmas = 0;
    //only construct first order model if optUseModel() is true
    if( optUseModel() ){
      if( optUseModel() ){
        //check if any quantifiers are un-initialized
        for( int i=0; i<fm->getNumAssertedQuantifiers(); i++ ){
          Node f = fm->getAssertedQuantifier( i );
          d_addedLemmas += initializeQuantifier( f );
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
}

int ModelEngineBuilder::initializeQuantifier( Node f ){
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
    std::vector< Node > terms;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      Node ic = d_qe->getTermDatabase()->getInstantiationConstant( f, j );
      Node t = d_qe->getTermDatabase()->getModelBasisTerm( ic.getType() );
      vars.push_back( f[0][j] );
      terms.push_back( t );
      //calculate the basis match for f
      d_quant_basis_match[f].set( ic, t);
    }
    ++(d_statistics.d_num_quants_init);
    if( optInstGen() ){
      //add model basis instantiation
      if( d_qe->addInstantiation( f, vars, terms ) ){
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
  if( optReconsiderFuncConstants() ){
    //reconsider constant functions that weren't necessary
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
  }
  if( !d_uf_model_constructed[op] ){
    //construct the model for the uninterpretted function/predicate
    bool setDefaultVal = true;
    Node defaultTerm = d_qe->getTermDatabase()->getModelBasisOpTerm( op );
    Debug("fmf-model-cons") << "Construct model for " << op << "..." << std::endl;
    //set the values in the model
    for( size_t i=0; i<fm->d_uf_terms[op].size(); i++ ){
      Node n = fm->d_uf_terms[op][i];
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
          if( shouldSetDefaultValue( n ) ){
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

bool ModelEngineBuilder::optReconsiderFuncConstants(){
  return false;
}

void ModelEngineBuilder::setEffort( int effort ){
  d_considerAxioms = effort>=1;
}

ModelEngineBuilder::Statistics::Statistics():
  d_pre_sat_quant("ModelEngineBuilder::Status_quant_pre_sat", 0),
  d_pre_nsat_quant("ModelEngineBuilder::Status_quant_pre_non_sat", 0),
  d_num_quants_init("ModelEngine::Num_Quants", 0 ),
  d_num_quants_init_fail("ModelEngine::Num_Quants_No_Basis", 0 )
{
  StatisticsRegistry::registerStat(&d_pre_sat_quant);
  StatisticsRegistry::registerStat(&d_pre_nsat_quant);
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_quants_init_fail);
}

ModelEngineBuilder::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_pre_sat_quant);
  StatisticsRegistry::unregisterStat(&d_pre_nsat_quant);
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_quants_init_fail);
}

bool ModelEngineBuilder::isQuantifierActive( Node f ){
  return ( d_considerAxioms || !f.getAttribute(AxiomAttribute()) ) && d_quant_sat.find( f )==d_quant_sat.end();
}





void ModelEngineBuilderDefault::analyzeQuantifiers( FirstOrderModel* fm ){
  d_quant_selection_lit.clear();
  d_quant_selection_lit_candidates.clear();
  d_quant_selection_lit_terms.clear();
  d_term_selection_lit.clear();
  d_op_selection_terms.clear();
  //analyze each quantifier
  for( int i=0; i<(int)fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    if( isQuantifierActive( f ) ){
      analyzeQuantifier( fm, f );
    }
  }
}


void ModelEngineBuilderDefault::analyzeQuantifier( FirstOrderModel* fm, Node f ){
  Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
  //the pro/con preferences for this quantifier
  std::vector< Node > pro_con[2];
  //the terms in the selection literal we choose
  std::vector< Node > selectionLitTerms;
  //for each asserted quantifier f,
  // - determine selection literals
  // - check which function/predicates have good and bad definitions for satisfying f
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
    ++(d_statistics.d_pre_sat_quant);
  }else{
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

int ModelEngineBuilderDefault::doInstGen( FirstOrderModel* fm, Node f ){
  int addedLemmas = 0;
  //we wish to add all known exceptions to our selection literal for f. this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  if( !d_quant_selection_lit[f].isNull() ){
    Trace("inst-gen") << "Do Inst-Gen for " << f << std::endl;
    for( size_t i=0; i<d_quant_selection_lit_candidates[f].size(); i++ ){
      bool phase = d_quant_selection_lit_candidates[f][i].getKind()!=NOT;
      Node lit = d_quant_selection_lit_candidates[f][i].getKind()==NOT ? d_quant_selection_lit_candidates[f][i][0] : d_quant_selection_lit_candidates[f][i];
      Assert( lit.hasAttribute(InstConstantAttribute()) );
      std::vector< Node > tr_terms;
      if( lit.getKind()==APPLY_UF ){
        //only match predicates that are contrary to this one, use literal matching
        std::vector< Node > children;
        children.push_back( lit );
        children.push_back( !phase ? fm->d_true : fm->d_false );
        Node eq = d_qe->getTermDatabase()->mkNodeInstConstant( IFF, children, f );
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
  }
  return addedLemmas;
}

bool ModelEngineBuilderDefault::shouldSetDefaultValue( Node n ){
  return n.hasAttribute(ModelBasisArgAttribute()) && n.getAttribute(ModelBasisArgAttribute())==1;
}





void ModelEngineBuilderInstGen::analyzeQuantifiers( FirstOrderModel* fm ){
  //for new inst gen
  d_quant_selection_formula.clear();
  d_term_selected.clear();
  //analyze each quantifier
  for( int i=0; i<(int)fm->getNumAssertedQuantifiers(); i++ ){
    Node f = fm->getAssertedQuantifier( i );
    if( isQuantifierActive( f ) ){
      analyzeQuantifier( fm, f );
    }
  }
  //analyze each partially instantiated quantifier
  for( std::map< Node, Node >::iterator it = d_sub_quant_parent.begin(); it != d_sub_quant_parent.end(); ++it ){
    Node fp = getParentQuantifier( it->first );
    if( isQuantifierActive( fp ) ){
      analyzeQuantifier( fm, it->first );
    }
  }
}

void ModelEngineBuilderInstGen::analyzeQuantifier( FirstOrderModel* fm, Node f ){
  //determine selection formula, set terms in selection formula as being selected
  Node s = getSelectionFormula( d_qe->getTermDatabase()->getInstConstantBody( f ),
                                d_qe->getTermDatabase()->getModelBasisBody( f ), true, 0 );
  //if( !s.isNull() ){
  //  s = Rewriter::rewrite( s );
  //}
  d_qe->getTermDatabase()->setInstantiationConstantAttr( s, f );
  Trace("sel-form") << "Selection formula " << f << std::endl;
  Trace("sel-form") << "                  " << s << std::endl;
  if( !s.isNull() ){
    d_quant_selection_formula[f] = s;
    Node gs = d_qe->getTermDatabase()->getModelBasis( f, s );
    setSelectedTerms( gs );
  }
}


int ModelEngineBuilderInstGen::doInstGen( FirstOrderModel* fm, Node f ){
  int addedLemmas = 0;
  //we wish to add all known exceptions to our selection literal for f. this will help to refine our current model.
  //This step is advantageous over exhaustive instantiation, since we are adding instantiations that involve model basis terms,
  //  effectively acting as partial instantiations instead of pointwise instantiations.
  if( !d_quant_selection_formula[f].isNull() ){
    //first, try on sub quantifiers
    for( size_t i=0; i<d_sub_quants[f].size(); i++ ){
      addedLemmas += doInstGen( fm, d_sub_quants[f][i] );
    }
    if( addedLemmas>0 ){
      return addedLemmas;
    }else{
      Node fp = getParentQuantifier( f );
      Trace("inst-gen") << "Do Inst-Gen for " << f << std::endl;
      Trace("inst-gen-debug") << "Calculate inst-gen instantiations..." << std::endl;
      //get all possible values of selection formula
      InstGenProcess igp( d_quant_selection_formula[f] );
      igp.calculateMatches( d_qe, f );
      Trace("inst-gen-debug") << "Add inst-gen instantiations (" << igp.getNumMatches() << ")..." << std::endl;
      for( int i=0; i<igp.getNumMatches(); i++ ){
        //if the match is not already true in the model
        if( igp.getMatchValue( i )!=fm->d_true ){
          InstMatch m;
          igp.getMatch( d_qe->getEqualityQuery(), i, m );
          //we only consider matches that are non-empty
          //  matches that are empty should trigger other instances that are non-empty
          if( !m.empty() ){
            bool addInst = false;
            Trace("inst-gen-debug") << "Get in terms of parent..." << std::endl;
            //translate to be in terms match in terms of fp
            InstMatch mp;
            getParentQuantifierMatch( mp, fp, m, f );

            //if this is a partial instantion
            if( !m.isComplete( f ) ){
              //if the instantiation does not yet exist
              if( d_sub_quant_inst_trie[fp].addInstMatch( d_qe, fp, mp, true ) ){
                //get the partial instantiation pf
                Node pf = d_qe->getInstantiation( fp, mp );
                Trace("inst-gen-pi") << "Partial instantiation of " << f << std::endl;
                Trace("inst-gen-pi") << "                         " << pf << std::endl;
                d_sub_quants[ f ].push_back( pf );
                d_sub_quant_inst[ pf ] = InstMatch( &mp );
                d_sub_quant_parent[ pf ] = fp;
                mp.add( d_quant_basis_match[ fp ] );
                addInst = true;
              }
            }else{
              addInst = true;
            }
            if( addInst ){
              //otherwise, get instantiation and add ground instantiation in terms of root parent
              if( d_qe->addInstantiation( fp, mp ) ){
                addedLemmas++;
              }
            }
          }
        }
      }
      if( addedLemmas==0 ){
        //all sub quantifiers must be satisfied as well
        bool subQuantSat = true;
        for( size_t i=0; i<d_sub_quants[f].size(); i++ ){
          if( d_quant_sat.find( d_sub_quants[f][i] )==d_quant_sat.end() ){
            subQuantSat = false;
            break;
          }
        }
        if( subQuantSat ){
          d_quant_sat[ f ] = true;
        }
      }
      Trace("inst-gen") << "  -> added lemmas = " << addedLemmas << std::endl;
    }
  }
  return addedLemmas;
}

bool ModelEngineBuilderInstGen::shouldSetDefaultValue( Node n ){
  return d_term_selected.find( n )!=d_term_selected.end();
}

//if possible, returns a formula n' such that n' => ( n <=> polarity ), and n' is true in the current context,
//   and NULL otherwise
Node ModelEngineBuilderInstGen::getSelectionFormula( Node fn, Node n, bool polarity, int useOption ){
  Trace("sel-form-debug") << "Looking for selection formula " << n << " " << polarity << std::endl;
  Node ret;
  if( n.getKind()==NOT ){
    ret = getSelectionFormula( fn[0], n[0], !polarity, useOption );
  }else if( n.getKind()==OR || n.getKind()==IMPLIES || n.getKind()==AND ){
    //whether we only need to find one or all
    bool posPol = (( n.getKind()==OR || n.getKind()==IMPLIES ) && polarity ) || ( n.getKind()==AND && !polarity );
    std::vector< Node > children;
    bool retSet = false;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      Node fnc = ( i==0 && fn.getKind()==IMPLIES ) ? fn[i].negate() : fn[i];
      Node nc = ( i==0 && n.getKind()==IMPLIES ) ? n[i].negate() : n[i];
      Node nn = getSelectionFormula( fnc, nc, polarity, useOption );
      if( nn.isNull()!=posPol ){   //TODO: may want to weaken selection formula
        ret = nn;
        retSet = true;
        break;
      }
      if( std::find( children.begin(), children.end(), nn )==children.end() ){
        children.push_back( nn );
      }
    }
    if( !retSet && !posPol ){
      ret = NodeManager::currentNM()->mkNode( AND, children );
    }
  }else if( n.getKind()==ITE ){
    Node nn;
    Node nc[2];
    //get selection formula for the
    for( int i=0; i<2; i++ ){
      nn = getSelectionFormula( fn[0], n[0], i==0, useOption );
      nc[i] = getSelectionFormula( fn[i+1], n[i+1], polarity, useOption );
      if( !nn.isNull() && !nc[i].isNull() ){
        ret = NodeManager::currentNM()->mkNode( AND, nn, nc[i] );
        break;
      }
    }
    if( ret.isNull() && !nc[0].isNull() && !nc[1].isNull() ){
      ret = NodeManager::currentNM()->mkNode( AND, nc[0], nc[1] );
    }
  }else if( n.getKind()==IFF || n.getKind()==XOR ){
    bool opPol = polarity ? n.getKind()==XOR : n.getKind()==IFF;
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
        ret = NodeManager::currentNM()->mkNode( AND, nn[0], nn[1] );
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
        }
      }
    }
  }
  Trace("sel-form-debug") << "   return " << ret << std::endl;
  return ret;
}

void ModelEngineBuilderInstGen::setSelectedTerms( Node s ){

  //if it is apply uf and has model basis arguments, then mark term as being "selected"
  if( s.getKind()==APPLY_UF ){
    Assert( s.hasAttribute(ModelBasisArgAttribute()) );
    if( !s.hasAttribute(ModelBasisArgAttribute()) ) std::cout << "no mba!! " << s << std::endl;
    if( s.getAttribute(ModelBasisArgAttribute())==1 ){
      d_term_selected[ s ] = true;
      Trace("sel-form-term") << "  " << s << " is a selected term." << std::endl;
    }
  }
  for( int i=0; i<(int)s.getNumChildren(); i++ ){
    setSelectedTerms( s[i] );
  }
}

bool ModelEngineBuilderInstGen::isUsableSelectionLiteral( Node n, int useOption ){
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

Node ModelEngineBuilderInstGen::getParentQuantifier( Node f ){
  std::map< Node, Node >::iterator it = d_sub_quant_parent.find( f );
  if( it==d_sub_quant_parent.end() || it->second.isNull() ){
    return f;
  }else{
    return it->second;
  }
}

void ModelEngineBuilderInstGen::getParentQuantifierMatch( InstMatch& mp, Node fp, InstMatch& m, Node f ){
  if( f!=fp ){
    //std::cout << "gpqm " << fp << " " << f << " " << m << std::endl;
    //std::cout << "     " << fp[0].getNumChildren() << " " << f[0].getNumChildren() << std::endl;
    int counter = 0;
    for( size_t i=0; i<fp[0].getNumChildren(); i++ ){
      Node icp = d_qe->getTermDatabase()->getInstantiationConstant( fp, i );
      if( counter<f[0].getNumChildren() ){
        if( fp[0][i]==f[0][counter] ){
          Node ic = d_qe->getTermDatabase()->getInstantiationConstant( f, counter );
          Node n = m.getValue( ic );
          if( !n.isNull() ){
            mp.setMatch( d_qe->getEqualityQuery(), icp, n );
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


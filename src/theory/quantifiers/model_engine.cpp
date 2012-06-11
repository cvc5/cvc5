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

//#define ME_PRINT_PROCESS_TIMES

//#define DISABLE_EVAL_SKIP_MULTIPLE
#define RECONSIDER_FUNC_DEFAULT_VALUE
#define RECONSIDER_FUNC_CONSTANT
#define USE_INDEX_ORDERING
//#define ONE_INST_PER_QUANT_PER_ROUND

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::quantifiers;

void printRepresentative( const char* c, QuantifiersEngine* qe, Node r ){
  if( r.getType()==NodeManager::currentNM()->booleanType() ){
    if( qe->getEqualityQuery()->areEqual( r, NodeManager::currentNM()->mkConst( true ) ) ){
      Debug( c ) << "true";
    }else{
      Debug( c ) << "false";
    }
  }else{
    Debug( c ) << qe->getEqualityQuery()->getRepresentative( r );
  }
}

RepAlphabet::RepAlphabet( RepAlphabet& ra, QuantifiersEngine* qe ){
  //translate to current representatives
  for( std::map< TypeNode, std::vector< Node > >::iterator it = ra.d_type_reps.begin(); it != ra.d_type_reps.end(); ++it ){
    std::vector< Node > reps;
    for( int i=0; i<(int)it->second.size(); i++ ){
      //reps.push_back( ie->getEqualityQuery()->getRepresentative( it->second[i] ) );
      reps.push_back( it->second[i] );
    }
    set( it->first, reps );
  }
}

void RepAlphabet::set( TypeNode t, std::vector< Node >& reps ){
  d_type_reps[t].insert( d_type_reps[t].begin(), reps.begin(), reps.end() );
  for( int i=0; i<(int)reps.size(); i++ ){
    d_tmap[ reps[i] ] = i;
  }
}

void RepAlphabet::debugPrint( const char* c, QuantifiersEngine* qe ){
  for( std::map< TypeNode, std::vector< Node > >::iterator it = d_type_reps.begin(); it != d_type_reps.end(); ++it ){
    Debug( c ) << it->first << " : " << std::endl;
    for( int i=0; i<(int)it->second.size(); i++ ){
      Debug( c ) << "   " << i << ": " << it->second[i] << std::endl;
      Debug( c ) << "         eq_class( " << it->second[i] << " ) : ";
      ((uf::InstantiatorTheoryUf*)qe->getInstantiator( THEORY_UF ))->outputEqClass( c, it->second[i] );
      Debug( c ) << std::endl;
    }
  }
}

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model ){
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    d_index_order.push_back( i );
  }
  initialize( qe, f, model );
}

RepAlphabetIterator::RepAlphabetIterator( QuantifiersEngine* qe, Node f, ModelEngine* model, std::vector< int >& indexOrder ){
  d_index_order.insert( d_index_order.begin(), indexOrder.begin(), indexOrder.end() );
  initialize( qe, f, model );
}

void RepAlphabetIterator::initialize( QuantifiersEngine* qe, Node f, ModelEngine* model ){
  d_f = f;
  d_model = model;
  //store instantiation constants
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    d_ic.push_back( qe->getInstantiationConstant( d_f, i ) );
    d_index.push_back( 0 );
  }
  //make the d_var_order mapping
  for( size_t i=0; i<d_index_order.size(); i++ ){
    d_var_order[d_index_order[i]] = i;
  }
  //for testing
  d_inst_tried = 0;
  d_inst_tests = 0;
}

void RepAlphabetIterator::increment2( QuantifiersEngine* qe, int counter ){
  Assert( !isFinished() );
  //increment d_index
  while( counter>=0 && d_index[counter]==(int)(d_model->getReps()->d_type_reps[d_f[0][d_index_order[counter]].getType()].size()-1) ){
    counter--;
  }
  if( counter==-1 ){
    d_index.clear();
  }else{
    for( int i=(int)d_index.size()-1; i>counter; i-- ){
      d_index[i] = 0;
      d_model->clearEvalFailed( i );
    }
    d_index[counter]++;
    d_model->clearEvalFailed( counter );
  }
}

void RepAlphabetIterator::increment( QuantifiersEngine* qe ){
  if( !isFinished() ){
    increment2( qe, (int)d_index.size()-1 );
  }
}

bool RepAlphabetIterator::isFinished(){
  return d_index.empty();
}

void RepAlphabetIterator::getMatch( QuantifiersEngine* ie, InstMatch& m ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    m.d_map[ ie->getInstantiationConstant( d_f, i ) ] = getTerm( i );
  }
}

Node RepAlphabetIterator::getTerm( int i ){
  TypeNode tn = d_f[0][d_index_order[i]].getType();
  Assert( d_model->getReps()->d_type_reps.find( tn )!=d_model->getReps()->d_type_reps.end() );
  return d_model->getReps()->d_type_reps[tn][d_index[d_index_order[i]]];
}

void RepAlphabetIterator::calculateTerms( QuantifiersEngine* qe ){
  d_terms.clear();
  for( int i=0; i<qe->getNumInstantiationConstants( d_f ); i++ ){
    d_terms.push_back( getTerm( i ) );
  }
}

void RepAlphabetIterator::debugPrint( const char* c ){
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << i << ": " << d_index[i] << ", (" << getTerm( i ) << " / " << d_ic[ i ] << std::endl;
  }
}

void RepAlphabetIterator::debugPrintSmall( const char* c ){
  Debug( c ) << "RI: ";
  for( int i=0; i<(int)d_index.size(); i++ ){
    Debug( c ) << d_index[i] << ": " << getTerm( i ) << " ";
  }
  Debug( c ) << std::endl;
}

//set value function
void UfModelTree::setValue( QuantifiersEngine* qe, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex ){
  if( d_data.empty() ){
    d_value = v;
  }else if( !d_value.isNull() && d_value!=v ){
    d_value = Node::null();
  }
  if( argIndex<(int)n.getNumChildren() ){
    //take r = null when argument is the model basis
    Node r;
    if( ground || !n[ indexOrder[argIndex] ].getAttribute(ModelBasisAttribute()) ){
      r = qe->getEqualityQuery()->getRepresentative( n[ indexOrder[argIndex] ] );
    }
    d_data[ r ].setValue( qe, n, v, indexOrder, ground, argIndex+1 );
  }
}

//get value function
Node UfModelTree::getValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex ){
  if( !d_value.isNull() && isTotal( n.getOperator(), argIndex ) ){
    //Notice() << "Constant, return " << d_value << ", depIndex = " << argIndex << std::endl;
    depIndex = argIndex;
    return d_value;
  }else{
    Node val;
    int childDepIndex[2] = { argIndex, argIndex };
    for( int i=0; i<2; i++ ){
      //first check the argument, then check default
      Node r;
      if( i==0 ){
        r = qe->getEqualityQuery()->getRepresentative( n[ indexOrder[argIndex] ] );
      }
      std::map< Node, UfModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        val = it->second.getValue( qe, n, indexOrder, childDepIndex[i], argIndex+1 );
        if( !val.isNull() ){
          break;
        }
      }else{
        //argument is not a defined argument: thus, it depends on this argument
        childDepIndex[i] = argIndex+1;
      }
    }
    //update depIndex
    depIndex = childDepIndex[0]>childDepIndex[1] ? childDepIndex[0] : childDepIndex[1];
    //Notice() << "Return " << val << ", depIndex = " << depIndex;
    //Notice() << " ( " << childDepIndex[0] << ", " << childDepIndex[1] << " )" << std::endl;
    return val;
  }
}

//simplify function
void UfModelTree::simplify( Node op, Node defaultVal, int argIndex ){
  if( argIndex<(int)op.getType().getNumChildren()-1 ){
    std::vector< Node > eraseData;
    //first process the default argument
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
        eraseData.push_back( r );
      }else{
        it->second.simplify( op, defaultVal, argIndex+1 );
        if( !it->second.d_value.isNull() && it->second.isTotal( op, argIndex+1 ) ){
          defaultVal = it->second.d_value;
        }else{
          defaultVal = Node::null();
        }
      }
    }
    //now see if any children can be removed, and simplify the ones that cannot
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        if( !defaultVal.isNull() && it->second.d_value==defaultVal ){
          eraseData.push_back( it->first );
        }else{
          it->second.simplify( op, defaultVal, argIndex+1 );
        }
      }
    }
    for( int i=0; i<(int)eraseData.size(); i++ ){
      d_data.erase( eraseData[i] );
    }
  }
}

//is total function
bool UfModelTree::isTotal( Node op, int argIndex ){
  if( argIndex==(int)(op.getType().getNumChildren()-1) ){
    return !d_value.isNull();
  }else{
    Node r;
    std::map< Node, UfModelTree >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      return it->second.isTotal( op, argIndex+1 );
    }else{
      return false;
    }
  }
}

Node UfModelTree::getConstantValue( QuantifiersEngine* qe, Node n, std::vector< int >& indexOrder, int argIndex ){
  return d_value;
}

void indent( const char* c, int ind ){
  for( int i=0; i<ind; i++ ){
    Debug( c ) << " ";
  }
}

void UfModelTree::debugPrint( const char* c, QuantifiersEngine* qe, std::vector< int >& indexOrder, int ind, int arg ){
  if( !d_data.empty() ){
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        indent( c, ind );
        Debug( c ) << "if x_" << indexOrder[arg] << " == " << it->first << std::endl;
        it->second.debugPrint( c, qe, indexOrder, ind+2, arg+1 );
      }
    }
    if( d_data.find( Node::null() )!=d_data.end() ){
      d_data[ Node::null() ].debugPrint( c, qe, indexOrder, ind, arg+1 );
    }
  }else{
    indent( c, ind );
    Debug( c ) << "return ";
    printRepresentative( c, qe, d_value );
    //Debug( c ) << " { ";
    //for( int i=0; i<(int)d_explicit.size(); i++ ){
    //  Debug( c ) << d_explicit[i] << " ";
    //}
    //Debug( c ) << "}";
    Debug( c ) << std::endl;
  }
}

UfModel::UfModel( Node op, ModelEngine* me ) : d_op( op ), d_me( me ), 
  d_model_constructed( false ), d_reconsider_model( false ){

  d_tree = UfModelTreeOrdered( op );  TypeNode tn = d_op.getType();  tn = tn[(int)tn.getNumChildren()-1];  Assert( tn==NodeManager::currentNM()->booleanType() || uf::StrongSolverTheoryUf::isRelevantType( tn ) );  //look at ground assertions
  for( int i=0; i<(int)d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_me->getQuantifiersEngine()->getTermDatabase()->d_op_map[ d_op ][i];
    bool add = true;
    if( n.getAttribute(NoMatchAttribute()) ){
      add = false;
      //determine if it has model basis attribute
      for( int j=0; j<(int)n.getNumChildren(); j++ ){
        if( n[j].getAttribute(ModelBasisAttribute()) ){
          add = true;
          break;
        }
      }
    }
    if( add ){
      d_ground_asserts.push_back( n );
      Node r = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n );
      d_ground_asserts_reps.push_back( r );
    }
  }
  //determine if it is constant
  if( !d_ground_asserts.empty() ){
    bool isConstant = true;
    for( int i=1; i<(int)d_ground_asserts.size(); i++ ){
      if( d_ground_asserts_reps[0]!=d_ground_asserts_reps[i] ){
        isConstant = false;
        break;
      }
    }
    if( isConstant ){
      //set constant value
      Node t = d_me->getModelBasisApplyUfTerm( d_op );
      Node r = d_ground_asserts_reps[0];
      setValue( t, r, false );
      setModel();
      d_reconsider_model = true;
      Debug("fmf-model-cons") << "Function " << d_op << " is the constant function ";
      printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), r );
      Debug("fmf-model-cons") << std::endl;
    }
  }
}

void UfModel::setValue( Node n, Node v, bool ground ){
  d_set_values[ ground ? 1 : 0 ][n] = v;
}

void UfModel::setModel(){
  makeModel( d_me->getQuantifiersEngine(), d_tree );
  d_model_constructed = true;
}

void UfModel::clearModel(){
  for( int k=0; k<2; k++ ){
    d_set_values[k].clear();
  }
  d_tree.clear();
  d_model_constructed = false;
}

Node UfModel::getConstantValue( QuantifiersEngine* qe, Node n ){
  if( d_model_constructed ){
    return d_tree.getConstantValue( qe, n );
  }else{
    return Node::null();
  }
}

bool UfModel::isConstant(){
  Node gn = d_me->getModelBasisApplyUfTerm( d_op );
  Node n = getConstantValue( d_me->getQuantifiersEngine(), gn );
  return !n.isNull();
}

void UfModel::buildModel(){
#ifdef RECONSIDER_FUNC_CONSTANT
  if( d_model_constructed ){
    if( d_reconsider_model ){
      //if we are allowed to reconsider default value, then see if the default value can be improved
      Node t = d_me->getModelBasisApplyUfTerm( d_op );
      Node v = d_set_values[0][t];
      if( d_value_pro_con[1][v].size()>d_value_pro_con[0][v].size() ){
        Debug("fmf-model-cons-debug") << "Consider changing the default value for " << d_op << std::endl;
        clearModel();
      }
    }
  }
#endif
  //now, construct models for each uninterpretted function/predicate
  if( !d_model_constructed ){
    Debug("fmf-model-cons") << "Construct model for " << d_op << "..." << std::endl;
    //now, set the values in the model
    for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
      Node n = d_ground_asserts[i];
      Node v = d_ground_asserts_reps[i];
      //if this assertion did not help the model, just consider it ground
      //set n = v in the model tree
      Debug("fmf-model-cons") << "  Set " << n << " = ";
      printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), v );
      Debug("fmf-model-cons") << std::endl;
      //set it as ground value
      setValue( n, v );
    }
    //set the default value
    //chose defaultVal based on heuristic (the best proportion of "pro" responses)
    Node defaultVal;
    double maxScore = -1;
    for( int i=0; i<(int)d_values.size(); i++ ){
      Node v = d_values[i];
      double score = ( 1.0 + (double)d_value_pro_con[0][v].size() )/( 1.0 + (double)d_value_pro_con[1][v].size() );
      Debug("fmf-model-cons") << "  - score( ";
      printRepresentative( "fmf-model-cons", d_me->getQuantifiersEngine(), v );
      Debug("fmf-model-cons") << " ) = " << score << std::endl;
      if( score>maxScore ){
        defaultVal = v;
        maxScore = score;
      }
    }
#ifdef RECONSIDER_FUNC_DEFAULT_VALUE
    if( maxScore<1.0 ){
      //consider finding another value, if possible
      Debug("fmf-model-cons-debug") << "Poor choice for default value, score = " << maxScore << std::endl;
      TypeNode tn = d_op.getType();
      Node newDefaultVal = d_me->getArbitraryElement( tn[(int)tn.getNumChildren()-1], d_values );
      if( !newDefaultVal.isNull() ){
        defaultVal = newDefaultVal;
        Debug("fmf-model-cons-debug") << "-> Change default value to ";
        printRepresentative( "fmf-model-cons-debug", d_me->getQuantifiersEngine(), defaultVal );
        Debug("fmf-model-cons-debug") << std::endl;
      }else{
        Debug("fmf-model-cons-debug") << "-> Could not find arbitrary element of type " << tn[(int)tn.getNumChildren()-1] << std::endl;
        Debug("fmf-model-cons-debug") << "      Excluding: ";
        for( int i=0; i<(int)d_values.size(); i++ ){
          Debug("fmf-model-cons-debug") << d_values[i] << " ";
        }
        Debug("fmf-model-cons-debug") << std::endl;
      }
    }
#endif
    Assert( !defaultVal.isNull() );
    //get the default term (this term must be defined non-ground in model)
    Node defaultTerm = d_me->getModelBasisApplyUfTerm( d_op );
    Debug("fmf-model-cons") << "  Choose ";
    printRepresentative("fmf-model-cons", d_me->getQuantifiersEngine(), defaultVal );
    Debug("fmf-model-cons") << " as default value (" << defaultTerm << ")" << std::endl;
    Debug("fmf-model-cons") << "     # quantifiers pro = " << d_value_pro_con[0][defaultVal].size() << std::endl;
    Debug("fmf-model-cons") << "     # quantifiers con = " << d_value_pro_con[1][defaultVal].size() << std::endl;
    setValue( defaultTerm, defaultVal, false );
    Debug("fmf-model-cons") << "  Making model...";
    setModel();
    Debug("fmf-model-cons") << "  Finished constructing model for " << d_op << "." << std::endl;
  }
}

void UfModel::setValuePreference( Node f, Node n, bool isPro ){
  Node v = d_me->getQuantifiersEngine()->getEqualityQuery()->getRepresentative( n );
  //Notice() << "Set value preference " << n << " = " << v << " " << isPro << std::endl;
  if( std::find( d_values.begin(), d_values.end(), v )==d_values.end() ){
    d_values.push_back( v );
  }
  int index = isPro ? 0 : 1;
  if( std::find( d_value_pro_con[index][v].begin(), d_value_pro_con[index][v].end(), f )==d_value_pro_con[index][v].end() ){
    d_value_pro_con[index][v].push_back( f );
  }
}

void UfModel::makeModel( QuantifiersEngine* qe, UfModelTreeOrdered& tree ){
  for( int k=0; k<2; k++ ){
    for( std::map< Node, Node >::iterator it = d_set_values[k].begin(); it != d_set_values[k].end(); ++it ){
      tree.setValue( qe, it->first, it->second, k==1 );
    }
  }
  tree.simplify();
}

void UfModel::debugPrint( const char* c ){
  //Debug( c ) << "Function " << d_op << std::endl;
  //Debug( c ) << "   Type: " << d_op.getType() << std::endl;
  //Debug( c ) << "   Ground asserts:" << std::endl;
  //for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
  //  Debug( c ) << "      " << d_ground_asserts[i] << " = ";
  //  printRepresentative( c, d_me->getQuantifiersEngine(), d_ground_asserts[i] );
  //  Debug( c ) << std::endl;
  //}
  //Debug( c ) << "   Model:" << std::endl;

  TypeNode t = d_op.getType();
  Debug( c ) << d_op << "( ";
  for( int i=0; i<(int)(t.getNumChildren()-1); i++ ){
    Debug( c ) << "x_" << i << " : " << t[i];
    if( i<(int)(t.getNumChildren()-2) ){
      Debug( c ) << ", ";
    }
  }
  Debug( c ) << " ) : " << t[(int)t.getNumChildren()-1] << std::endl;
  if( d_tree.isEmpty() ){
    Debug( c ) << "   [undefined]" << std::endl;
  }else{
    d_tree.debugPrint( c, d_me->getQuantifiersEngine(), 3 );
    Debug( c ) << std::endl;
  }
  //Debug( c ) << "   Phase reqs:" << std::endl;  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::vector< Node > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
  //    Debug( c ) << "      " << it->first << std::endl;
  //    for( int j=0; j<(int)it->second.size(); j++ ){
  //      Debug( c ) << "         " << it->second[j] << " -> " << (i==1) << std::endl;
  //    }
  //  }
  //}
  //Debug( c ) << std::endl;
  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_eq_reqs[i].begin(); it != d_eq_reqs[i].end(); ++it ){
  //    Debug( c ) << "      " << "For " << it->first << ":" << std::endl;
  //    for( std::map< Node, std::vector< Node > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
  //      for( int j=0; j<(int)it2->second.size(); j++ ){
  //        Debug( c ) << "         " << it2->first << ( i==1 ? "==" : "!=" ) << it2->second[j] << std::endl;
  //      }
  //    }
  //  }
  //}
}

//Model Engine constructor
ModelEngine::ModelEngine( TheoryQuantifiers* th ){
  d_th = th;
  d_quantEngine = th->getQuantifiersEngine();
  d_ss = ((uf::TheoryUF*)d_quantEngine->getTheoryEngine()->getTheory( THEORY_UF ))->getStrongSolver();
}

void ModelEngine::check( Theory::Effort e ){
  if( e==Theory::EFFORT_LAST_CALL ){
    bool quantsInit = true;
    //first, check if we can minimize the model further
    if( !d_ss->minimize() ){
      return;
    }
    if( useModel() ){
      //now, check if any quantifiers are un-initialized
      for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getAssertedQuantifier( i );
        if( !initializeQuantifier( f ) ){
          quantsInit = false;
        }
      }
    }
    if( quantsInit ){
#ifdef ME_PRINT_PROCESS_TIMES
      Notice() << "---Instantiation Round---" << std::endl;
#endif
      Debug("fmf-model-debug") << "---Begin Instantiation Round---" << std::endl;
      ++(d_statistics.d_inst_rounds);
      d_quantEngine->getTermDatabase()->reset( e );
      //build the representatives
      Debug("fmf-model-debug") << "Building representatives..." << std::endl;
      buildRepresentatives();
      if( useModel() ){
        //initialize the model
        Debug("fmf-model-debug") << "Initializing model..." << std::endl;
        initializeModel();
        //analyze the quantifiers
        Debug("fmf-model-debug") << "Analyzing quantifiers..." << std::endl;
        analyzeQuantifiers();
        //build the model
        Debug("fmf-model-debug") << "Building model..." << std::endl;
        for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
          it->second.buildModel();
        }
      }
      //print debug
      debugPrint("fmf-model-complete");
      //try exhaustive instantiation
      Debug("fmf-model-debug") << "Do exhaustive instantiation..." << std::endl;
      int addedLemmas = 0;
      for( int i=0; i<d_quantEngine->getNumAssertedQuantifiers(); i++ ){
        Node f = d_quantEngine->getAssertedQuantifier( i );
        if( d_quant_sat.find( f )==d_quant_sat.end() ){
          addedLemmas += instantiateQuantifier( f );
        }
      }
#ifdef ME_PRINT_PROCESS_TIMES
      Notice() << "Added Lemmas = " << addedLemmas << std::endl;
#endif
      if( addedLemmas==0 ){
        //debugPrint("fmf-consistent");
        //for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
        //  it->second.simplify();
        //}
        Debug("fmf-consistent") << std::endl;
        debugPrint("fmf-consistent");
      }
    }
    d_quantEngine->flushLemmas( &d_th->getOutputChannel() );
  }
}

void ModelEngine::registerQuantifier( Node f ){

}

void ModelEngine::assertNode( Node f ){

}

bool ModelEngine::useModel() {
  return Options::current()->fmfModelBasedInst;
}

bool ModelEngine::initializeQuantifier( Node f ){
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

    std::vector< Node > terms;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      terms.push_back( getModelBasisTerm( f[0][j].getType() ) );
    }
    ++(d_statistics.d_num_quants_init);
    if( d_quantEngine->addInstantiation( f, terms ) ){
      return false;
    }else{
      //usually shouldn't happen
      //Notice() << "No model basis for " << f << std::endl;
      ++(d_statistics.d_num_quants_init_fail);
    }
  }
  return true;
}

void ModelEngine::buildRepresentatives(){
  d_ra.clear();
  //collect all representatives for all types and store as representative alphabet
  for( int i=0; i<d_ss->getNumCardinalityTypes(); i++ ){
    TypeNode tn = d_ss->getCardinalityType( i );
    std::vector< Node > reps;
    d_ss->getRepresentatives( tn, reps );
    Assert( !reps.empty() );
    //if( (int)reps.size()!=d_ss->getCardinality( tn ) ){
    //  Notice() << "InstStrategyFinteModelFind::processResetInstantiationRound: Bad representatives for type." << std::endl;
    //  Notice() << "   " << tn << " has cardinality " << d_ss->getCardinality( tn );
    //  Notice() << " but only " << (int)reps.size() << " were given." << std::endl;
    //  Unimplemented( 27 );
    //}
    Debug("fmf-model-debug") << "   " << tn << " -> " << reps.size() << std::endl;
    Debug("fmf-model-debug") << "      ";
    for( int i=0; i<(int)reps.size(); i++ ){
      Debug("fmf-model-debug") << reps[i] << " ";
    }
    Debug("fmf-model-debug") << std::endl;
    //set them in the alphabet
    d_ra.set( tn, reps );
#ifdef ME_PRINT_PROCESS_TIMES
    Notice() << tn << " has " << reps.size() << " representatives. " << std::endl;
#endif
  }
}

void ModelEngine::initializeModel(){
  d_uf_model.clear();
  d_quant_sat.clear();
  for( int k=0; k<2; k++ ){
    d_pro_con_quant[k].clear();
  }

  ////now analyze quantifiers (temporary)
  //for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
  //  Node f = d_quantEngine->getAssertedQuantifier( i );
  //  Debug("fmf-model-req") << "Phase requirements for " << f << ": " << std::endl;
  //  for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
  //       it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
  //    Node n = it->first;
  //    Debug("fmf-model-req") << "   " << n << " -> " << it->second << std::endl;
  //    if( n.getKind()==APPLY_UF ){
  //      processPredicate( f, n, it->second );
  //    }else if( n.getKind()==EQUAL ){
  //      processEquality( f, n, it->second );
  //    }
  //  }
  //}
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    initializeUf( f[1] );
    //register model basis terms
    std::vector< Node > vars;
    std::vector< Node > subs;
    for( int j=0; j<(int)f[0].getNumChildren(); j++ ){
      vars.push_back( d_quantEngine->getInstantiationConstant( f, j ) );
      subs.push_back( getModelBasisTerm( f[0][j].getType() ) );
    }
    Node n = d_quantEngine->getCounterexampleBody( f );
    Node gn = n.substitute( vars.begin(), vars.end(), subs.begin(), subs.end() );
    registerModelBasis( n, gn );
  }
}

void ModelEngine::analyzeQuantifiers(){
  int quantSatInit = 0;
  int nquantSatInit = 0;
  //analyze the preferences of each quantifier
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug("fmf-model-prefs") << "Analyze quantifier " << f << std::endl;
    std::vector< Node > pro_con[2];
    std::vector< Node > pro_con_patterns[2];
    //check which model basis terms have good and bad definitions according to f
    for( std::map< Node, bool >::iterator it = d_quantEngine->d_phase_reqs[f].begin();
         it != d_quantEngine->d_phase_reqs[f].end(); ++it ){
      Node n = it->first;
      Node gn = d_model_basis[n];
      Debug("fmf-model-req") << "   Req: " << n << " -> " << it->second << std::endl;
      int pref = 0;
      bool isConst = true;
      std::vector< Node > uf_terms;
      std::vector< Node > uf_term_patterns;
      if( gn.getKind()==APPLY_UF ){
        if( d_quantEngine->getEqualityQuery()->hasTerm( gn ) ){
          uf_terms.push_back( gn );
          uf_term_patterns.push_back( n );
          bool phase = areEqual( gn, NodeManager::currentNM()->mkConst( true ) );
          pref = phase!=it->second ? 1 : -1;
        }
      }else if( gn.getKind()==EQUAL ){
        bool success = true;
        for( int j=0; j<2; j++ ){
          if( n[j].getKind()==APPLY_UF ){
            Node op = gn[j].getOperator();
            if( d_uf_model.find( op )!=d_uf_model.end() ){
              Assert( gn[j].getKind()==APPLY_UF );
              uf_terms.push_back( gn[j] );
              uf_term_patterns.push_back( n[j] );
            }else{
              //found undefined uf operator
              success = false;
            }
          }else if( n[j].hasAttribute(InstConstantAttribute()) ){
            isConst = false;
          }
        }
        if( success && !uf_terms.empty() ){
          if( (!it->second && areEqual( gn[0], gn[1] )) || (it->second && areDisequal( gn[0], gn[1] )) ){
            pref = 1;
          }else if( (it->second && areEqual( gn[0], gn[1] )) || (!it->second && areDisequal( gn[0], gn[1] )) ){
            pref = -1;
          }
        }
      }
      if( pref!=0 ){
        Debug("fmf-model-prefs") << "  It is " << ( pref==1 ? "pro" : "con" );
        Debug("fmf-model-prefs") << " the definition of " << n << std::endl;
        if( pref==1 ){
          if( isConst ){
            for( int j=0; j<(int)uf_terms.size(); j++ ){
              //the only uf that is initialized are those that are constant
              Node op = uf_terms[j].getOperator();
              Assert( d_uf_model.find( op )!=d_uf_model.end() );
              if( !d_uf_model[op].isConstant() ){
                isConst = false;
                break;
              }
            }
            if( isConst ){
              d_quant_sat[f] = true;
              //we only need to consider current term definition(s) for this quantifier to be satisified, ignore the others
              for( int k=0; k<2; k++ ){
                pro_con[k].clear();
                pro_con_patterns[k].clear();
              } 
              //instead, just note to the model for each uf term that f is pro its definition
              for( int j=0; j<(int)uf_terms.size(); j++ ){
                Node op = uf_terms[j].getOperator();
                d_uf_model[op].d_reconsider_model = false;
              }
            }
          }
        }
        if( d_quant_sat.find( f )!=d_quant_sat.end() ){
          Debug("fmf-model-prefs") << "  * Constant SAT due to definition of " << n << std::endl;
          break;
        }else{
          int pcIndex = pref==1 ? 0 : 1;
          for( int j=0; j<(int)uf_terms.size(); j++ ){
            pro_con[pcIndex].push_back( uf_terms[j] );
            pro_con_patterns[pcIndex].push_back( uf_term_patterns[j] );
          }
        }
      }
    }
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      quantSatInit++;
      d_statistics.d_pre_sat_quant += quantSatInit;
    }else{
      nquantSatInit++;
      d_statistics.d_pre_nsat_quant += quantSatInit;
    }
    //add quantifier's preferences to vector
    for( int k=0; k<2; k++ ){
      for( int j=0; j<(int)pro_con[k].size(); j++ ){
        Node op = pro_con[k][j].getOperator();
        d_uf_model[op].setValuePreference( f, pro_con[k][j], k==0 );
        d_pro_con_quant[k][ f ].push_back( pro_con_patterns[k][j] );
      }
    }
  }
  Debug("fmf-model-prefs") << "Pre-Model Completion: Quantifiers SAT: " << quantSatInit << " / " << (quantSatInit+nquantSatInit) << std::endl;
}

int ModelEngine::instantiateQuantifier( Node f ){
  int addedLemmas = 0;
  Debug("inst-fmf-ei") << "Add matches for " << f << "..." << std::endl;
  Debug("inst-fmf-ei") << "   Instantiation Constants: ";
  for( size_t i=0; i<f[0].getNumChildren(); i++ ){
    Debug("inst-fmf-ei") << d_quantEngine->getInstantiationConstant( f, i ) << " ";
  }
  Debug("inst-fmf-ei") << std::endl;
  for( int k=0; k<2; k++ ){
    Debug("inst-fmf-ei") << "  " << ( k==0 ? "Pro" : "Con" ) << " definitions:" << std::endl;
    for( int i=0; i<(int)d_pro_con_quant[k][f].size(); i++ ){
      Debug("inst-fmf-ei") << "    " << d_pro_con_quant[k][f][i] << std::endl;
    }
  }
  if( d_pro_con_quant[0][f].empty() ){
    Debug("inst-fmf-ei") << "WARNING: " << f << " has no pros for default literal definitions" << std::endl;
  }
  d_eval_failed_lits.clear();
  d_eval_failed.clear();
  d_eval_term_model.clear();
  //d_eval_term_vals.clear();
  //d_eval_term_fv_deps.clear();
  RepAlphabetIterator riter( d_quantEngine, f, this );
  increment( &riter );
#ifdef ONE_INST_PER_QUANT_PER_ROUND
  while( !riter.isFinished() && addedLemmas==0 ){
#else
  while( !riter.isFinished() ){
#endif
    InstMatch m;
    riter.getMatch( d_quantEngine, m );
    Debug("fmf-model-eval") << "* Add instantiation " << std::endl;
    riter.d_inst_tried++;
    if( d_quantEngine->addInstantiation( f, m ) ){
      addedLemmas++;
    }
    riter.increment( d_quantEngine );
    increment( &riter );
  }
  if( Debug.isOn("inst-fmf-ei") ){
    int totalInst = 1;
    for( int i=0; i<(int)f[0].getNumChildren(); i++ ){
      totalInst = totalInst * (int)getReps()->d_type_reps[ f[0][i].getType() ].size();
    }
    Debug("inst-fmf-ei") << "Finished: " << std::endl;
    Debug("inst-fmf-ei") << "   Inst Skipped: " << (totalInst-riter.d_inst_tried) << std::endl;
    Debug("inst-fmf-ei") << "   Inst Tried: " << riter.d_inst_tried << std::endl;
    Debug("inst-fmf-ei") << "   Inst Added: " << addedLemmas << std::endl;
    Debug("inst-fmf-ei") << "   # Tests: " << riter.d_inst_tests << std::endl;
  }
  return addedLemmas;
}

void ModelEngine::registerModelBasis( Node n, Node gn ){
  if( d_model_basis.find( n )==d_model_basis.end() ){
    d_model_basis[n] = gn;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      registerModelBasis( n[i], gn[i] );
    }
  }
}

Node ModelEngine::getArbitraryElement( TypeNode tn, std::vector< Node >& exclude ){
  Node retVal;
  if( tn==NodeManager::currentNM()->booleanType() ){
    if( exclude.empty() ){
      retVal = NodeManager::currentNM()->mkConst( false );
    }else if( exclude.size()==1 ){
      retVal = NodeManager::currentNM()->mkConst( areEqual( exclude[0], NodeManager::currentNM()->mkConst( false ) ) );
    }
  }else if( d_ra.d_type_reps.find( tn )!=d_ra.d_type_reps.end() ){
    for( int i=0; i<(int)d_ra.d_type_reps[tn].size(); i++ ){
      if( std::find( exclude.begin(), exclude.end(), d_ra.d_type_reps[tn][i] )==exclude.end() ){
        retVal = d_ra.d_type_reps[tn][i];
        break;
      }
    }
  }
  if( !retVal.isNull() ){
    return d_quantEngine->getEqualityQuery()->getRepresentative( retVal );
  }else{
    return Node::null();
  }
}

Node ModelEngine::getModelBasisTerm( TypeNode tn, int i ){
  return d_ss->getCardinalityTerm( tn );
}

Node ModelEngine::getModelBasisApplyUfTerm( Node op ){
  if( d_model_basis_term.find( op )==d_model_basis_term.end() ){
    TypeNode t = op.getType();
    std::vector< Node > children;
    children.push_back( op );
    for( int i=0; i<(int)t.getNumChildren()-1; i++ ){
      children.push_back( getModelBasisTerm( t[i] ) );
    }
    d_model_basis_term[op] = NodeManager::currentNM()->mkNode( APPLY_UF, children );
  }
  return d_model_basis_term[op];
}

bool ModelEngine::isModelBasisTerm( Node op, Node n ){
  if( n.getOperator()==op ){
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( !n[i].getAttribute(ModelBasisAttribute()) ){
        return false;
      }
    }
    return true;
  }else{
    return false;
  }
}

void ModelEngine::initializeUf( Node n ){
  std::vector< Node > terms;
  collectUfTerms( n, terms );
  for( int i=0; i<(int)terms.size(); i++ ){
    initializeUfModel( terms[i].getOperator() );
  }
}

void ModelEngine::collectUfTerms( Node n, std::vector< Node >& terms ){
  if( n.getKind()==APPLY_UF ){
    terms.push_back( n );
  }
  for( int i=0; i<(int)n.getNumChildren(); i++ ){
    collectUfTerms( n[i], terms );
  }
}

void ModelEngine::initializeUfModel( Node op ){
  if( d_uf_model.find( op )==d_uf_model.end() ){
    TypeNode tn = op.getType();
    tn = tn[ (int)tn.getNumChildren()-1 ];
    if( tn==NodeManager::currentNM()->booleanType() || uf::StrongSolverTheoryUf::isRelevantType( tn ) ){
      d_uf_model[ op ] = UfModel( op, this );
    }
  }
}

void ModelEngine::makeEvalTermModel( Node n ){
  if( d_eval_term_model.find( n )==d_eval_term_model.end() ){
    makeEvalTermIndexOrder( n );
    if( !d_eval_term_use_default_model[n] ){
      Node op = n.getOperator();
      d_eval_term_model[n] = UfModelTreeOrdered( op, d_eval_term_index_order[n] );
      d_uf_model[op].makeModel( d_quantEngine, d_eval_term_model[n] );
      Debug("fmf-model-index-order") << "Make model for " << n << " : " << std::endl;
      d_eval_term_model[n].debugPrint( "fmf-model-index-order", d_quantEngine, 2 );
    }
  }
}

struct sortGetMaxVariableNum {
  std::map< Node, int > d_max_var_num;
  int computeMaxVariableNum( Node n ){
    if( n.getKind()==INST_CONSTANT ){
      return n.getAttribute(InstVarNumAttribute());
    }else if( n.hasAttribute(InstConstantAttribute()) ){
      int maxVal = -1;
      for( int i=0; i<(int)n.getNumChildren(); i++ ){
        int val = getMaxVariableNum( n[i] );
        if( val>maxVal ){
          maxVal = val;
        }
      }
      return maxVal;
    }else{
      return -1;
    }
  }
  int getMaxVariableNum( Node n ){
    std::map< Node, int >::iterator it = d_max_var_num.find( n );
    if( it==d_max_var_num.end() ){
      int num = computeMaxVariableNum( n );
      d_max_var_num[n] = num;
      return num;
    }else{
      return it->second;
    }
  }
  bool operator() (Node i,Node j) { return (getMaxVariableNum(i)<getMaxVariableNum(j));}
};

void ModelEngine::makeEvalTermIndexOrder( Node n ){
  if( d_eval_term_index_order.find( n )==d_eval_term_index_order.end() ){
    //sort arguments in order of least significant vs. most significant variable in default ordering
    std::map< Node, std::vector< int > > argIndex;
    std::vector< Node > args;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      if( argIndex.find( n[i] )==argIndex.end() ){
        args.push_back( n[i] );
      }
      argIndex[n[i]].push_back( i );
    }
    sortGetMaxVariableNum sgmvn;
    std::sort( args.begin(), args.end(), sgmvn );
    for( int i=0; i<(int)args.size(); i++ ){
      for( int j=0; j<(int)argIndex[ args[i] ].size(); j++ ){
        d_eval_term_index_order[n].push_back( argIndex[ args[i] ][j] );
      }
    }
    bool useDefault = true;
    for( int i=0; i<(int)d_eval_term_index_order[n].size(); i++ ){
      if( i!=d_eval_term_index_order[n][i] ){
        useDefault = false;
        break;
      }
    }
    d_eval_term_use_default_model[n] = useDefault;
    Debug("fmf-model-index-order") << "Will consider the following index ordering for " << n << " : ";
    for( int i=0; i<(int)d_eval_term_index_order[n].size(); i++ ){
      Debug("fmf-model-index-order") << d_eval_term_index_order[n][i] << " ";
    }
    Debug("fmf-model-index-order") << std::endl;
  }
}

//void ModelEngine::processPredicate( Node f, Node p, bool phase ){
//  Node op = p.getOperator();
//  initializeUfModel( op );
//  d_uf_model[ op ].addRequirement( f, p, phase );
//}
//
//void ModelEngine::processEquality( Node f, Node eq, bool phase ){
//  for( int i=0; i<2; i++ ){
//    int j = i==0 ? 1 : 0;
//    if( eq[i].getKind()==APPLY_UF && eq[i].hasAttribute(InstConstantAttribute()) ){
//      Node op = eq[i].getOperator();
//      initializeUfModel( op );
//      d_uf_model[ op ].addEqRequirement( f, eq[i], eq[j], phase );
//    }
//  }
//}

void ModelEngine::increment( RepAlphabetIterator* rai ){
  if( useModel() ){
    bool success;
    do{
      success = true;
      if( !rai->isFinished() ){
        //see if instantiation is already true in current model
        Debug("fmf-model-eval") << "Evaulating ";
        rai->debugPrintSmall("fmf-model-eval");
        //calculate represenative terms we are currently considering
        rai->calculateTerms( d_quantEngine );
        rai->d_inst_tests++;
        //if eVal is not (int)rai->d_index.size(), then the instantiation is already true in the model,
        // and eVal is the highest index in rai which we can safely iterate
        int depIndex;
        if( evaluate( rai, d_quantEngine->getCounterexampleBody( rai->d_f ), depIndex )==1 ){
          Debug("fmf-model-eval") << "  Returned success with depIndex = " << depIndex << std::endl;
          //Notice() << "Returned eVal = " << eVal << "/" << rai->d_index.size() << std::endl;
          if( depIndex<(int)rai->d_index.size() ){
#ifdef DISABLE_EVAL_SKIP_MULTIPLE
            depIndex = (int)rai->d_index.size()-1;
#endif
            rai->increment2( d_quantEngine, depIndex );
            success = false;
          }
        }else{
          Debug("fmf-model-eval") << "  Returned failure." << std::endl;
        }
      }
    }while( !success );
  }
}

//if evaluate( rai, n, phaseReq ) = eVal,
// if eVal = rai->d_index.size()
//   then the formula n instantiated with rai cannot be proven to be equal to phaseReq
// otherwise,
//   each n{rai->d_index[0]/x_0...rai->d_index[eVal]/x_eVal, */x_(eVal+1) ... */x_n } is equal to phaseReq in the current model
int ModelEngine::evaluate( RepAlphabetIterator* rai, Node n, int& depIndex ){
  ++(d_statistics.d_eval_formulas);
  //Debug("fmf-model-eval-debug") << "Evaluate " << n << " " << phaseReq << std::endl;
  if( n.getKind()==NOT ){
    int val = evaluate( rai, n[0], depIndex );
    return val==1 ? -1 : ( val==-1 ? 1 : 0 );
  }else if( n.getKind()==OR || n.getKind()==AND || n.getKind()==IMPLIES ){
    int baseVal = n.getKind()==AND ? 1 : -1;
    int eVal = baseVal;
    int posDepIndex = (int)rai->d_index.size();
    int negDepIndex = -1;
    for( int i=0; i<(int)n.getNumChildren(); i++ ){
      //evaluate subterm
      int childDepIndex;
      Node nn = ( i==0 && n.getKind()==IMPLIES ) ? n[i].notNode() : n[i];
      int eValT = evaluate( rai, nn, childDepIndex );
      if( eValT==baseVal ){
        if( eVal==baseVal ){
          if( childDepIndex>negDepIndex ){
            negDepIndex = childDepIndex;
          }
        }
      }else if( eValT==-baseVal ){
        eVal = -baseVal;
        if( childDepIndex<posDepIndex ){
          posDepIndex = childDepIndex;
          if( posDepIndex==-1 ){
            break;
          }
        }
      }else if( eValT==0 ){
        if( eVal==baseVal ){
          eVal = 0;
        }
      }
    }
    if( eVal!=0 ){
      depIndex = eVal==-baseVal ? posDepIndex : negDepIndex;
      return eVal;
    }else{
      return 0;
    }
  }else if( n.getKind()==IFF || n.getKind()==XOR ){
    int depIndex1;
    int eVal = evaluate( rai, n[0], depIndex1 );
    if( eVal!=0 ){
      int depIndex2;
      int eVal2 = evaluate( rai, n.getKind()==XOR ? n[1].notNode() : n[1], depIndex2 );
      if( eVal2!=0 ){
        depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
        return eVal==eVal2 ? 1 : -1;
      }
    }
    return 0;
  }else if( n.getKind()==ITE ){
    int depIndex1;
    int eVal = evaluate( rai, n[0], depIndex1 );
    if( eVal==0 ){
      //DO_THIS: evaluate children to see if they are the same value?
      return 0;
    }else{
      int depIndex2;
      int eValT = evaluate( rai, n[eVal==1 ? 1 : 2], depIndex2 );
      depIndex = depIndex1>depIndex2 ? depIndex1 : depIndex2;
      return eValT;
    }
  }else if( n.getKind()==FORALL ){
    return 0;
  }else{
    ////if we know we will fail again, immediately return
    //if( d_eval_failed.find( n )!=d_eval_failed.end() ){
    //  if( d_eval_failed[n] ){
    //    return -1;
    //  }
    //}
    //Debug("fmf-model-eval-debug") << "Evaluate literal " << n << std::endl;
    //this should be a literal
    Node gn = n.substitute( rai->d_ic.begin(), rai->d_ic.end(), rai->d_terms.begin(), rai->d_terms.end() );
    //Debug("fmf-model-eval-debug") << "  Ground version = " << gn << std::endl;
    int retVal = 0;
    std::vector< Node > fv_deps;
    if( n.getKind()==APPLY_UF ){
      //case for boolean predicates
      Node val = evaluateTerm( n, gn, fv_deps );
      if( d_quantEngine->getEqualityQuery()->hasTerm( val ) ){
        if( areEqual( val, NodeManager::currentNM()->mkConst( true ) ) ){
          retVal = 1;
        }else{
          retVal = -1;
        }
      }
    }else if( n.getKind()==EQUAL ){
      //case for equality
      retVal = evaluateEquality( n[0], n[1], gn[0], gn[1], fv_deps );
    }
    if( retVal!=0 ){
      int maxIndex = -1;
      for( int i=0; i<(int)fv_deps.size(); i++ ){
        int index = rai->d_var_order[ fv_deps[i].getAttribute(InstVarNumAttribute()) ];
        if( index>maxIndex ){
          maxIndex = index;
          if( index==(int)rai->d_index.size()-1 ){
            break;
          }
        }
      }
      Debug("fmf-model-eval-debug") << "Evaluate literal: return " << retVal << ", depends = " << maxIndex << std::endl;
      depIndex = maxIndex;
    }
    return retVal;
  }
}

int ModelEngine::evaluateEquality( Node n1, Node n2, Node gn1, Node gn2, std::vector< Node >& fv_deps ){
  ++(d_statistics.d_eval_eqs);
  Debug("fmf-model-eval-debug") << "Evaluate equality: " << std::endl;
  Debug("fmf-model-eval-debug") << "   " << n1 << " = " << n2 << std::endl;
  Debug("fmf-model-eval-debug") << "   " << gn1 << " = " << gn2 << std::endl;
  Node val1 = evaluateTerm( n1, gn1, fv_deps );
  Node val2 = evaluateTerm( n2, gn2, fv_deps );
  Debug("fmf-model-eval-debug") << "   Values :  ";
  printRepresentative( "fmf-model-eval-debug", d_quantEngine, val1 );
  Debug("fmf-model-eval-debug") <<  " = ";
  printRepresentative( "fmf-model-eval-debug", d_quantEngine, val2 );
  Debug("fmf-model-eval-debug") << std::endl;
  int retVal = 0;
  if( areEqual( val1, val2 ) ){
    retVal = 1;
  }else if( areDisequal( val1, val2 ) ){
    retVal = -1;
  }
  if( retVal!=0 ){
    Debug("fmf-model-eval-debug") << "   ---> Success, value = " << (retVal==1) << std::endl;
  }else{
    Debug("fmf-model-eval-debug") << "   ---> Failed" << std::endl;
  }
  Debug("fmf-model-eval-debug") << "       Value depends on variables: ";
  for( int i=0; i<(int)fv_deps.size(); i++ ){
    Debug("fmf-model-eval-debug") << fv_deps[i] << " ";
  }
  Debug("fmf-model-eval-debug") << std::endl;
  return retVal;
}

Node ModelEngine::evaluateTerm( Node n, Node gn, std::vector< Node >& fv_deps ){
  if( n.hasAttribute(InstConstantAttribute()) ){
    if( n.getKind()==INST_CONSTANT ){
      fv_deps.push_back( n );
      return gn;
    //}else if( d_eval_term_fv_deps.find( n )!=d_eval_term_fv_deps.end() && 
    //          d_eval_term_fv_deps[n].find( gn )!=d_eval_term_fv_deps[n].end() ){
    //  fv_deps.insert( fv_deps.end(), d_eval_term_fv_deps[n][gn].begin(), d_eval_term_fv_deps[n][gn].end() );
    //  return d_eval_term_vals[gn];
    }else{
      //Debug("fmf-model-eval-debug") << "Evaluate term " << n << " (" << gn << ")" << std::endl;
      //first we must evaluate the arguments
      Node val = gn;
      if( n.getKind()==APPLY_UF ){
        Node op = gn.getOperator();
        //if it is a defined UF, then consult the interpretation
        Node gnn = gn;
        ++(d_statistics.d_eval_uf_terms);
        int depIndex = 0;
        //first we must evaluate the arguments
        bool childrenChanged = false;
        std::vector< Node > children;
        children.push_back( op );
        std::map< int, std::vector< Node > > children_var_deps;
        //for each argument, calculate its value, and the variables its value depends upon
        for( int i=0; i<(int)n.getNumChildren(); i++ ){
          Node nn = evaluateTerm( n[i], gn[i], children_var_deps[i] );
          children.push_back( nn );
          childrenChanged = childrenChanged || nn!=gn[i];
        }
        //remake gn if changed
        if( childrenChanged ){
          gnn = NodeManager::currentNM()->mkNode( APPLY_UF, children );
        }
        if( d_uf_model.find( op )!=d_uf_model.end() ){
#ifdef USE_INDEX_ORDERING
          //make the term model specifically for n
          makeEvalTermModel( n );
          //now, consult the model
          if( d_eval_term_use_default_model[n] ){
            val = d_uf_model[op].d_tree.getValue( d_quantEngine, gnn, depIndex );
          }else{
            val = d_eval_term_model[ n ].getValue( d_quantEngine, gnn, depIndex );
          }
          //Debug("fmf-model-eval-debug") << "Evaluate term " << n << " (" << gn << ", " << gnn << ")" << std::endl;
          //d_eval_term_model[ n ].debugPrint("fmf-model-eval-debug", d_quantEngine );
          Assert( !val.isNull() );
#else
          //now, consult the model
          val = d_uf_model[op].d_tree.getValue( d_quantEngine, gnn, depIndex );
#endif
        }else{
          d_eval_term_use_default_model[n] = true;
          val = gnn;
          depIndex = (int)n.getNumChildren();
        }
        Debug("fmf-model-eval-debug") << "Evaluate term " << n << " = " << gn << " = " << gnn << " = ";
        printRepresentative( "fmf-model-eval-debug", d_quantEngine, val );
        Debug("fmf-model-eval-debug") << ", depIndex = " << depIndex << std::endl;
        if( !val.isNull() ){
#ifdef USE_INDEX_ORDERING
          for( int i=0; i<depIndex; i++ ){
            int index = d_eval_term_use_default_model[n] ? i : d_eval_term_index_order[n][i];
            Debug("fmf-model-eval-debug") << "Add variables from " << index << "..." << std::endl;
            fv_deps.insert( fv_deps.end(), children_var_deps[index].begin(),
                            children_var_deps[index].end() );
          }
#else
          //calculate the free variables that the value depends on : take those in children_var_deps[0...depIndex-1]
          for( std::map< int, std::vector< Node > >::iterator it = children_var_deps.begin(); it != children_var_deps.end(); ++it ){
            if( it->first<depIndex ){
              fv_deps.insert( fv_deps.end(), it->second.begin(), it->second.end() );
            }
          }
#endif
        }
        ////cache the result
        //d_eval_term_vals[gn] = val;
        //d_eval_term_fv_deps[n][gn].insert( d_eval_term_fv_deps[n][gn].end(), fv_deps.begin(), fv_deps.end() );
      }
      return val;
    }
  }else{
    return n;
  }
}

void ModelEngine::clearEvalFailed( int index ){
  for( int i=0; i<(int)d_eval_failed_lits[index].size(); i++ ){
    d_eval_failed[ d_eval_failed_lits[index][i] ] = false;
  }
  d_eval_failed_lits[index].clear();
}

bool ModelEngine::areEqual( Node a, Node b ){
  return d_quantEngine->getEqualityQuery()->areEqual( a, b );
}

bool ModelEngine::areDisequal( Node a, Node b ){
  return d_quantEngine->getEqualityQuery()->areDisequal( a, b );
}

void ModelEngine::debugPrint( const char* c ){
  Debug( c ) << "---Current Model---" << std::endl;
  Debug( c ) << "Representatives: " << std::endl;
  d_ra.debugPrint( c, d_quantEngine );
  Debug( c ) << "Quantifiers: " << std::endl;
  for( int i=0; i<(int)d_quantEngine->getNumAssertedQuantifiers(); i++ ){
    Node f = d_quantEngine->getAssertedQuantifier( i );
    Debug( c ) << "   ";
    if( d_quant_sat.find( f )!=d_quant_sat.end() ){
      Debug( c ) << "*SAT* ";
    }else{
      Debug( c ) << "      ";
    }
    Debug( c ) << f << std::endl;
  }
  Debug( c ) << "Functions: " << std::endl;
  for( std::map< Node, UfModel >::iterator it = d_uf_model.begin(); it != d_uf_model.end(); ++it ){
    it->second.debugPrint( c );
    Debug( c ) << std::endl;
  }
}

ModelEngine::Statistics::Statistics():
  d_inst_rounds("ModelEngine::Inst_Rounds", 0),
  d_pre_sat_quant("ModelEngine::Status_quant_pre_sat", 0),
  d_pre_nsat_quant("ModelEngine::Status_quant_pre_non_sat", 0),
  d_eval_formulas("ModelEngine::Eval_Formulas", 0 ),
  d_eval_eqs("ModelEngine::Eval_Equalities", 0 ),
  d_eval_uf_terms("ModelEngine::Eval_Uf_Terms", 0 ),
  d_num_quants_init("ModelEngine::Num_Quants", 0 ),
  d_num_quants_init_fail("ModelEngine::Num_Quants_No_Basis", 0 )
{
  StatisticsRegistry::registerStat(&d_inst_rounds);
  StatisticsRegistry::registerStat(&d_pre_sat_quant);
  StatisticsRegistry::registerStat(&d_pre_nsat_quant);
  StatisticsRegistry::registerStat(&d_eval_formulas);
  StatisticsRegistry::registerStat(&d_eval_eqs);
  StatisticsRegistry::registerStat(&d_eval_uf_terms);
  StatisticsRegistry::registerStat(&d_num_quants_init);
  StatisticsRegistry::registerStat(&d_num_quants_init_fail);
}

ModelEngine::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_inst_rounds);
  StatisticsRegistry::unregisterStat(&d_pre_sat_quant);
  StatisticsRegistry::unregisterStat(&d_pre_nsat_quant);
  StatisticsRegistry::unregisterStat(&d_eval_formulas);
  StatisticsRegistry::unregisterStat(&d_eval_eqs);
  StatisticsRegistry::unregisterStat(&d_eval_uf_terms);
  StatisticsRegistry::unregisterStat(&d_num_quants_init);
  StatisticsRegistry::unregisterStat(&d_num_quants_init_fail);
}

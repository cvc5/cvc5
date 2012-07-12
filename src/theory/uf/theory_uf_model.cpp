/*********************                                                        */
/*! \file theory_uf_model.cpp
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
 ** \brief Implementation of Theory UF Model
 **/

#include "theory/quantifiers/model_engine.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"
#include "theory/uf/theory_uf_strong_solver.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

#define RECONSIDER_FUNC_DEFAULT_VALUE
#define USE_PARTIAL_DEFAULT_VALUES

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

//clear
void UfModelTree::clear(){
  d_data.clear();
  d_value = Node::null();
}

bool UfModelTree::hasConcreteArgumentDefinition(){
  if( d_data.size()>1 ){
    return true;
  }else if( d_data.empty() ){
    return false;
  }else{
    Node r;
    return d_data.find( r )==d_data.end();
  }
}

//set value function
void UfModelTree::setValue( TheoryModel* m, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex ){
  if( d_data.empty() ){
    d_value = v;
  }else if( !d_value.isNull() && d_value!=v ){
    d_value = Node::null();
  }
  if( argIndex<(int)n.getNumChildren() ){
    //take r = null when argument is the model basis
    Node r;
    if( ground || !n[ indexOrder[argIndex] ].getAttribute(ModelBasisAttribute()) ){
      r = m->getRepresentative( n[ indexOrder[argIndex] ] );
    }
    d_data[ r ].setValue( m, n, v, indexOrder, ground, argIndex+1 );
  }
}

//get value function
Node UfModelTree::getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex ){
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
        r = m->getRepresentative( n[ indexOrder[argIndex] ] );
      }
      std::map< Node, UfModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        val = it->second.getValue( m, n, indexOrder, childDepIndex[i], argIndex+1 );
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

Node UfModelTree::getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, std::vector< int >& depIndex, int argIndex ){
  if( argIndex==(int)indexOrder.size() ){
    return d_value;
  }else{
    Node val;
    bool depArg = false;
    //will try concrete value first, then default
    for( int i=0; i<2; i++ ){
      Node r;
      if( i==0 ){
        r = m->getRepresentative( n[ indexOrder[argIndex] ] );
      }
      std::map< Node, UfModelTree >::iterator it = d_data.find( r );
      if( it!=d_data.end() ){
        val = it->second.getValue( m, n, indexOrder, depIndex, argIndex+1 );
        //we have found a value
        if( !val.isNull() ){
          if( i==0 ){
            depArg = true;
          }
          break;
        }
      }
    }
    //it depends on this argument if we found it via concrete argument value,
    // or if found by default/disequal from some concrete argument value(s).
    if( depArg || hasConcreteArgumentDefinition() ){
      if( std::find( depIndex.begin(), depIndex.end(), indexOrder[argIndex] )==depIndex.end() ){
        depIndex.push_back( indexOrder[argIndex] );
      }
    }
    return val;
  }
}

Node UfModelTree::getFunctionValue(){
  if( !d_data.empty() ){
    Node defaultValue;
    std::vector< Node > caseValues;
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( it->first.isNull() ){
        defaultValue = it->second.getFunctionValue();
      }else{
        caseValues.push_back( NodeManager::currentNM()->mkNode( FUNCTION_CASE, it->first, it->second.getFunctionValue() ) );
      }
    }
    if( caseValues.empty() && defaultValue.getKind()!=FUNCTION_CASE_SPLIT && defaultValue.getKind()!=FUNCTION_MODEL ){
      return defaultValue;
    }else{
      std::vector< Node > children;
      if( !caseValues.empty() ){
        children.push_back( NodeManager::currentNM()->mkNode( FUNCTION_CASE_SPLIT, caseValues ) );
      }
      if( !defaultValue.isNull() ){
        children.push_back( defaultValue );
      }
      return NodeManager::currentNM()->mkNode( FUNCTION_MODEL, children );
    }
  }else{
    Assert( !d_value.isNull() );
    return d_value;
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
          if( it->second.isEmpty() ){
            eraseData.push_back( r );
          }
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
          if( it->second.isEmpty() ){
            eraseData.push_back( it->first );
          }
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

Node UfModelTree::getConstantValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int argIndex ){
  return d_value;
}

void indent( std::ostream& out, int ind ){
  for( int i=0; i<ind; i++ ){
    out << " ";
  }
}

void UfModelTree::debugPrint( std::ostream& out, TheoryModel* m, std::vector< int >& indexOrder, int ind, int arg ){
  if( !d_data.empty() ){
    for( std::map< Node, UfModelTree >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
      if( !it->first.isNull() ){
        indent( out, ind );
        out << "if x_" << indexOrder[arg] << " == " << it->first << std::endl;
        it->second.debugPrint( out, m, indexOrder, ind+2, arg+1 );
      }
    }
    if( d_data.find( Node::null() )!=d_data.end() ){
      d_data[ Node::null() ].debugPrint( out, m, indexOrder, ind, arg+1 );
    }
  }else{
    indent( out, ind );
    out << "return ";
    m->printRepresentative( out, d_value );
    //out << " { ";
    //for( int i=0; i<(int)d_explicit.size(); i++ ){
    //  out << d_explicit[i] << " ";
    //}
    //out << "}";
    out << std::endl;
  }
}

UfModel::UfModel( Node op, quantifiers::FirstOrderModel* m ) : d_model( m ), d_op( op ),
d_model_constructed( false ){
  d_tree = UfModelTreeOrdered( op );
  TypeNode tn = d_op.getType();
  tn = tn[(int)tn.getNumChildren()-1];
  Assert( tn==NodeManager::currentNM()->booleanType() || tn.isDatatype() || uf::StrongSolverTheoryUf::isRelevantType( tn ) );
  //look at ground assertions
  for( size_t i=0; i<d_model->getTermDatabase()->d_op_map[ d_op ].size(); i++ ){
    Node n = d_model->getTermDatabase()->d_op_map[ d_op ][i];
    d_model->getTermDatabase()->computeModelBasisArgAttribute( n );
    if( !n.getAttribute(NoMatchAttribute()) || n.getAttribute(ModelBasisArgAttribute())==1 ){
      Node r = d_model->getRepresentative( n );
      d_ground_asserts_reps.push_back( r );
      d_ground_asserts.push_back( n );
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
      Node t = d_model->getTermDatabase()->getModelBasisOpTerm( d_op );
      Node r = d_ground_asserts_reps[0];
      setValue( t, r, false );
      setModel();
      Debug("fmf-model-cons") << "Function " << d_op << " is the constant function ";
      d_model->printRepresentativeDebug( "fmf-model-cons", r );
      Debug("fmf-model-cons") << std::endl;
    }
  }
}

Node UfModel::getIntersection( Node n1, Node n2, bool& isGround ){
  //Notice() << "Get intersection " << n1 << " " << n2 << std::endl;
  isGround = true;
  std::vector< Node > children;
  children.push_back( n1.getOperator() );
  for( int i=0; i<(int)n1.getNumChildren(); i++ ){
    if( n1[i]==n2[i] ){
      if( n1[i].getAttribute(ModelBasisAttribute()) ){
        isGround = false;
      }
      children.push_back( n1[i] );
    }else if( n1[i].getAttribute(ModelBasisAttribute()) ){
      children.push_back( n2[i] );
    }else if( n2[i].getAttribute(ModelBasisAttribute()) ){
      children.push_back( n1[i] );
    }else if( d_model->areEqual( n1[i], n2[i] ) ){
      children.push_back( n1[i] );
    }else{
      return Node::null();
    }
  }
  return NodeManager::currentNM()->mkNode( APPLY_UF, children );
}

void UfModel::setValue( Node n, Node v, bool ground, bool isReq ){
  Assert( !n.isNull() );
  Assert( !v.isNull() );
  d_set_values[ isReq ? 1 : 0 ][ ground ? 1 : 0 ][n] = v;
  if( optUsePartialDefaults() ){
    if( !ground ){
      int defSize = (int)d_defaults.size();
      for( int i=0; i<defSize; i++ ){
        bool isGround;
        //for soundness, to allow variable order-independent function interpretations,
        //  we must ensure that the intersection of all default terms
        //  is also defined.
        //for example, if we have that f( e, a ) = ..., and f( b, e ) = ...,
        //  then we must define f( b, a ).
        Node ni = getIntersection( n, d_defaults[i], isGround );
        if( !ni.isNull() ){
          //if the intersection exists, and is not already defined
          if( d_set_values[0][ isGround ? 1 : 0 ].find( ni )==d_set_values[0][ isGround ? 1 : 0 ].end() &&
              d_set_values[1][ isGround ? 1 : 0 ].find( ni )==d_set_values[1][ isGround ? 1 : 0 ].end() ){
            //use the current value
            setValue( ni, v, isGround, false );
          }
        }
      }
      d_defaults.push_back( n );
    }
    if( isReq && d_set_values[0][ ground ? 1 : 0 ].find( n )!=d_set_values[0][ ground ? 1 : 0 ].end()){
      d_set_values[0][ ground ? 1 : 0 ].erase( n );
    }
  }
}

Node UfModel::getValue( Node n, int& depIndex ){
  return d_tree.getValue( d_model, n, depIndex );
}

Node UfModel::getValue( Node n, std::vector< int >& depIndex ){
  return d_tree.getValue( d_model, n, depIndex );
}

Node UfModel::getConstantValue( Node n ){
  if( d_model_constructed ){
    return d_tree.getConstantValue( d_model, n );
  }else{
    return Node::null();
  }
}

Node UfModel::getFunctionValue(){
  if( d_func_value.isNull() && d_model_constructed ){
    d_func_value = d_tree.getFunctionValue();
  }
  return d_func_value;
}

bool UfModel::isConstant(){
  Node gn = d_model->getTermDatabase()->getModelBasisOpTerm( d_op );
  Node n = getConstantValue( gn );
  return !n.isNull();
}

bool UfModel::optUsePartialDefaults(){
#ifdef USE_PARTIAL_DEFAULT_VALUES
  return true;
#else
  return false;
#endif
}

void UfModel::setModel(){
  makeModel( d_tree );
  d_model_constructed = true;
  d_func_value = Node::null();

  //for debugging, make sure model satisfies all ground assertions
  for( size_t i=0; i<d_ground_asserts.size(); i++ ){
    int depIndex;
    Node n = d_tree.getValue( d_model, d_ground_asserts[i], depIndex );
    if( n!=d_ground_asserts_reps[i] ){
      Debug("fmf-bad") << "Bad model : " << d_ground_asserts[i] << " := ";
      d_model->printRepresentativeDebug("fmf-bad", n );
      Debug("fmf-bad") << " != ";
      d_model->printRepresentativeDebug("fmf-bad", d_ground_asserts_reps[i] );
      Debug("fmf-bad") << std::endl;
    }
  }
}

void UfModel::clearModel(){
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      d_set_values[j][k].clear();
    }
  }
  d_tree.clear();
  d_model_constructed = false;
}

void UfModel::makeModel( UfModelTreeOrdered& tree ){
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      for( std::map< Node, Node >::iterator it = d_set_values[j][k].begin(); it != d_set_values[j][k].end(); ++it ){
        tree.setValue( d_model, it->first, it->second, k==1 );
      }
    }
  }
  tree.simplify();
}

void UfModel::toStream(std::ostream& out){
  //out << "Function " << d_op << std::endl;
  //out << "   Type: " << d_op.getType() << std::endl;
  //out << "   Ground asserts:" << std::endl;
  //for( int i=0; i<(int)d_ground_asserts.size(); i++ ){
  //  out << "      " << d_ground_asserts[i] << " = ";
  //  d_model->printRepresentative( out, d_ground_asserts[i] );
  //  out << std::endl;
  //}
  //out << "   Model:" << std::endl;

  TypeNode t = d_op.getType();
  out << d_op << "( ";
  for( int i=0; i<(int)(t.getNumChildren()-1); i++ ){
    out << "x_" << i << " : " << t[i];
    if( i<(int)(t.getNumChildren()-2) ){
      out << ", ";
    }
  }
  out << " ) : " << t[(int)t.getNumChildren()-1] << std::endl;
  if( d_tree.isEmpty() ){
    out << "   [undefined]" << std::endl;
  }else{
    d_tree.debugPrint( out, d_model, 3 );
    out << std::endl;
  }
  //out << "   Phase reqs:" << std::endl;  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::vector< Node > >::iterator it = d_reqs[i].begin(); it != d_reqs[i].end(); ++it ){
  //    out << "      " << it->first << std::endl;
  //    for( int j=0; j<(int)it->second.size(); j++ ){
  //      out << "         " << it->second[j] << " -> " << (i==1) << std::endl;
  //    }
  //  }
  //}
  //out << std::endl;
  //for( int i=0; i<2; i++ ){
  //  for( std::map< Node, std::map< Node, std::vector< Node > > >::iterator it = d_eq_reqs[i].begin(); it != d_eq_reqs[i].end(); ++it ){
  //    out << "      " << "For " << it->first << ":" << std::endl;
  //    for( std::map< Node, std::vector< Node > >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
  //      for( int j=0; j<(int)it2->second.size(); j++ ){
  //        out << "         " << it2->first << ( i==1 ? "==" : "!=" ) << it2->second[j] << std::endl;
  //      }
  //    }
  //  }
  //}
}

Node UfModel::toIte2( Node fm_node, std::vector< Node >& args, int index, Node defaultNode ){
  if( fm_node.getKind()==FUNCTION_MODEL ){
    if( fm_node[0].getKind()==FUNCTION_CASE_SPLIT ){
      Node retNode;
      Node childDefaultNode = defaultNode;
      //get new default
      if( fm_node.getNumChildren()==2 ){
        childDefaultNode = toIte2( fm_node[1], args, index+1, defaultNode );
      }
      retNode = childDefaultNode;
      for( int i=(int)fm_node[0].getNumChildren()-1; i>=0; i-- ){
        Node childNode = toIte2( fm_node[0][1], args, index+1, childDefaultNode );
        retNode = NodeManager::currentNM()->mkNode( ITE, args[index].eqNode( fm_node[0][0] ), childNode, retNode );
      }
      return retNode;
    }else{
      return toIte2( fm_node[0], args, index+1, defaultNode );
    }
  }else{
    return fm_node;
  }
}


void UfModelPreferenceData::setValuePreference( Node f, Node n, Node r, bool isPro ){
  if( std::find( d_values.begin(), d_values.end(), r )==d_values.end() ){
    d_values.push_back( r );
  }
  int index = isPro ? 0 : 1;
  if( std::find( d_value_pro_con[index][r].begin(), d_value_pro_con[index][r].end(), f )==d_value_pro_con[index][r].end() ){
    d_value_pro_con[index][r].push_back( f );
  }
  d_term_pro_con[index][n].push_back( f );
}

Node UfModelPreferenceData::getBestDefaultValue( Node defaultTerm, TheoryModel* m ){
  Node defaultVal;
  double maxScore = -1;
  for( size_t i=0; i<d_values.size(); i++ ){
    Node v = d_values[i];
    double score = ( 1.0 + (double)d_value_pro_con[0][v].size() )/( 1.0 + (double)d_value_pro_con[1][v].size() );
    Debug("fmf-model-cons") << "  - score( ";
    m->printRepresentativeDebug( "fmf-model-cons", v );
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
    TypeNode tn = defaultTerm.getType();
    Node newDefaultVal = m->getDomainValue( tn, d_values );
    if( !newDefaultVal.isNull() ){
      defaultVal = newDefaultVal;
      Debug("fmf-model-cons-debug") << "-> Change default value to ";
      m->printRepresentativeDebug( "fmf-model-cons-debug", defaultVal );
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
  //get the default term (this term must be defined non-ground in model)
  Debug("fmf-model-cons") << "  Choose ";
  m->printRepresentativeDebug("fmf-model-cons", defaultVal );
  Debug("fmf-model-cons") << " as default value (" << defaultTerm << ")" << std::endl;
  Debug("fmf-model-cons") << "     # quantifiers pro = " << d_value_pro_con[0][defaultVal].size() << std::endl;
  Debug("fmf-model-cons") << "     # quantifiers con = " << d_value_pro_con[1][defaultVal].size() << std::endl;
  return defaultVal;
}
/*********************                                                        */
/*! \file theory_uf_model.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Theory UF Model
 **/

#include "theory/uf/theory_uf_model.h"

#include <stack>
#include <vector>

#include "expr/attribute.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/theory_engine.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/theory_uf.h"


#define RECONSIDER_FUNC_DEFAULT_VALUE
#define USE_PARTIAL_DEFAULT_VALUES

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::uf;

//clear
void UfModelTreeNode::clear(){
  d_data.clear();
  d_value = Node::null();
}

bool UfModelTreeNode::hasConcreteArgumentDefinition(){
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
void UfModelTreeNode::setValue( TheoryModel* m, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex ){
  if( d_data.empty() ){
    //overwrite value if either at leaf or this is a fresh tree
    d_value = v;
  }else if( !d_value.isNull() && d_value!=v ){
    //value is no longer constant
    d_value = Node::null();
  }
  if( argIndex<(int)indexOrder.size() ){
    //take r = null when argument is the model basis
    Node r;
    if( ground || ( !n.isNull() && !n[ indexOrder[argIndex] ].getAttribute(ModelBasisAttribute()) ) ){
      r = m->getRepresentative( n[ indexOrder[argIndex] ] );
    }
    d_data[ r ].setValue( m, n, v, indexOrder, ground, argIndex+1 );
  }
}

//get value function
Node UfModelTreeNode::getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex ){
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
      std::map< Node, UfModelTreeNode >::iterator it = d_data.find( r );
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

Node UfModelTreeNode::getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, std::vector< int >& depIndex, int argIndex ){
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
      std::map< Node, UfModelTreeNode >::iterator it = d_data.find( r );
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

Node UfModelTreeNode::getFunctionValue(std::vector<Node>& args, int index, Node argDefaultValue, bool simplify) {
  if(!d_data.empty()) {
    Node defaultValue = argDefaultValue;
    if(d_data.find(Node::null()) != d_data.end()) {
      defaultValue = d_data[Node::null()].getFunctionValue(args, index + 1, argDefaultValue, simplify);
    }

    vector<Node> caseArgs;
    map<Node, Node> caseValues;

    for(map< Node, UfModelTreeNode>::iterator it = d_data.begin(); it != d_data.end(); ++it) {
      if(!it->first.isNull()) {
        Node val = it->second.getFunctionValue(args, index + 1, defaultValue, simplify);
        caseArgs.push_back(it->first);
        caseValues[it->first] = val;
      }
    }

    NodeManager* nm = NodeManager::currentNM();
    Node retNode = defaultValue;

    if(!simplify) {
      // "non-simplifying" mode - expand function values to things like:
      //   IF      (x=0 AND y=0 AND z=0) THEN value1
      //   ELSE IF (x=0 AND y=0 AND z=1) THEN value2
      //   [...etc...]
      for(int i = (int)caseArgs.size() - 1; i >= 0; --i) {
        Node val = caseValues[ caseArgs[ i ] ];
        if(val.getKind() == ITE) {
          // use a stack to reverse the order, since we're traversing outside-in
          stack<TNode> stk;
          do {
            stk.push(val);
            val = val[2];
          } while(val.getKind() == ITE);
          AlwaysAssert(val == defaultValue, "default values don't match when constructing function definition!");
          while(!stk.empty()) {
            val = stk.top();
            stk.pop();
            retNode = nm->mkNode(ITE, nm->mkNode(AND, args[index].eqNode(caseArgs[i]), val[0]), val[1], retNode);
          }
        } else {
          retNode = nm->mkNode(ITE, args[index].eqNode(caseArgs[i]), caseValues[caseArgs[i]], retNode);
        }
      }
    } else {
      // "simplifying" mode - condense function values
      for(int i = (int)caseArgs.size() - 1; i >= 0; --i) {
        retNode = nm->mkNode(ITE, args[index].eqNode(caseArgs[i]), caseValues[caseArgs[i]], retNode);
      }
    }
    return retNode;
  } else {
    Assert(!d_value.isNull());
    return d_value;
  }
}

//update function
void UfModelTreeNode::update( TheoryModel* m ){
  if( !d_value.isNull() ){
    d_value = m->getRepresentative( d_value );
  }
  std::map< Node, UfModelTreeNode > old = d_data;
  d_data.clear();
  for( std::map< Node, UfModelTreeNode >::iterator it = old.begin(); it != old.end(); ++it ){
    Node rep = m->getRepresentative( it->first );
    d_data[ rep ] = it->second;
    d_data[ rep ].update( m );
  }
}

//simplify function
void UfModelTreeNode::simplify( Node op, Node defaultVal, int argIndex ){
  if( argIndex<(int)op.getType().getNumChildren()-1 ){
    std::vector< Node > eraseData;
    //first process the default argument
    Node r;
    std::map< Node, UfModelTreeNode >::iterator it = d_data.find( r );
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
    for( std::map< Node, UfModelTreeNode >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
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
bool UfModelTreeNode::isTotal( Node op, int argIndex ){
  if( argIndex==(int)(op.getType().getNumChildren()-1) ){
    return !d_value.isNull();
  }else{
    Node r;
    std::map< Node, UfModelTreeNode >::iterator it = d_data.find( r );
    if( it!=d_data.end() ){
      return it->second.isTotal( op, argIndex+1 );
    }else{
      return false;
    }
  }
}

Node UfModelTreeNode::getConstantValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int argIndex ){
  return d_value;
}

void indent( std::ostream& out, int ind ){
  for( int i=0; i<ind; i++ ){
    out << " ";
  }
}

void UfModelTreeNode::debugPrint( std::ostream& out, TheoryModel* m, std::vector< int >& indexOrder, int ind, int arg ){
  if( !d_data.empty() ){
    for( std::map< Node, UfModelTreeNode >::iterator it = d_data.begin(); it != d_data.end(); ++it ){
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
    out << std::endl;
  }
}

Node UfModelTree::getFunctionValue( std::vector< Node >& args, bool simplify ){
  Node body = d_tree.getFunctionValue( args, 0, Node::null(), simplify );
  if(simplify) {
    body = Rewriter::rewrite( body );
  }
  Node boundVarList = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args);
  return NodeManager::currentNM()->mkNode(kind::LAMBDA, boundVarList, body);
}

Node UfModelTree::getFunctionValue( const char* argPrefix, bool simplify ){
  TypeNode type = d_op.getType();
  std::vector< Node > vars;
  for( size_t i=0; i<type.getNumChildren()-1; i++ ){
    std::stringstream ss;
    ss << argPrefix << (i+1);
    vars.push_back( NodeManager::currentNM()->mkBoundVar( ss.str(), type[i] ) );
  }
  return getFunctionValue( vars, simplify );
}

Node UfModelTreeGenerator::getIntersection( TheoryModel* m, Node n1, Node n2, bool& isGround ){
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
    }else if( m->areEqual( n1[i], n2[i] ) ){
      children.push_back( n1[i] );
    }else{
      return Node::null();
    }
  }
  return NodeManager::currentNM()->mkNode( APPLY_UF, children );
}

void UfModelTreeGenerator::setValue( TheoryModel* m, Node n, Node v, bool ground, bool isReq ){
  Assert( !n.isNull() );
  Assert( !v.isNull() );
  d_set_values[ isReq ? 1 : 0 ][ ground ? 1 : 0 ][n] = v;
  if( optUsePartialDefaults() ){
    if( !ground ){
      int defSize = (int)d_defaults.size();
      for( int i=0; i<defSize; i++ ){
        //for soundness, to allow variable order-independent function interpretations,
        //  we must ensure that the intersection of all default terms
        //  is also defined.
        //for example, if we have that f( e, a ) = ..., and f( b, e ) = ...,
        //  then we must define f( b, a ).
        bool isGround;
        Node ni = getIntersection( m, n, d_defaults[i], isGround );
        if( !ni.isNull() ){
          //if the intersection exists, and is not already defined
          if( d_set_values[0][ isGround ? 1 : 0 ].find( ni )==d_set_values[0][ isGround ? 1 : 0 ].end() &&
              d_set_values[1][ isGround ? 1 : 0 ].find( ni )==d_set_values[1][ isGround ? 1 : 0 ].end() ){
            //use the current value
            setValue( m, ni, v, isGround, false );
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

void UfModelTreeGenerator::makeModel( TheoryModel* m, UfModelTree& tree ){
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      for( std::map< Node, Node >::iterator it = d_set_values[j][k].begin(); it != d_set_values[j][k].end(); ++it ){
        tree.setValue( m, it->first, it->second, k==1 );
      }
    }
  }
  if( !d_default_value.isNull() ){
    tree.setDefaultValue( m, d_default_value );
  }
  tree.simplify();
}

bool UfModelTreeGenerator::optUsePartialDefaults(){
#ifdef USE_PARTIAL_DEFAULT_VALUES
  return true;
#else
  return false;
#endif
}

void UfModelTreeGenerator::clear(){
  d_default_value = Node::null();
  for( int j=0; j<2; j++ ){
    for( int k=0; k<2; k++ ){
      d_set_values[j][k].clear();
    }
  }
  d_defaults.clear();
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
    Debug("fmf-model-cons-debug") << "  - score( ";
    m->printRepresentativeDebug( "fmf-model-cons-debug", v );
    Debug("fmf-model-cons-debug") << " ) = " << score << std::endl;
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
    Node newDefaultVal = m->getRepSet()->getDomainValue(tn, d_values);
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
  Debug("fmf-model-cons-debug") << "  Choose ";
  m->printRepresentativeDebug("fmf-model-cons-debug", defaultVal );
  Debug("fmf-model-cons-debug") << " as default value (" << defaultTerm << ")" << std::endl;
  Debug("fmf-model-cons-debug") << "     # quantifiers pro = " << d_value_pro_con[0][defaultVal].size() << std::endl;
  Debug("fmf-model-cons-debug") << "     # quantifiers con = " << d_value_pro_con[1][defaultVal].size() << std::endl;
  return defaultVal;
}

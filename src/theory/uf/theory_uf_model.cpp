/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Theory UF Model.
 */

#include "theory/uf/theory_uf_model.h"

#include <stack>

#include "expr/attribute.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/rewriter.h"
#include "theory/theory_model.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

//clear
void UfModelTreeNode::clear(){
  d_data.clear();
  d_value = Node::null();
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
    if (ground
        || (!n.isNull()
            && !quantifiers::FirstOrderModel::isModelBasis(
                   n[indexOrder[argIndex]])))
    {
      r = m->getRepresentative( n[ indexOrder[argIndex] ] );
    }
    d_data[ r ].setValue( m, n, v, indexOrder, ground, argIndex+1 );
  }
}

Node UfModelTreeNode::getFunctionValue(const std::vector<Node>& args,
                                       int index,
                                       Node argDefaultValue)
{
  if(!d_data.empty()) {
    Node defaultValue = argDefaultValue;
    if(d_data.find(Node::null()) != d_data.end()) {
      defaultValue = d_data[Node::null()].getFunctionValue(
          args, index + 1, argDefaultValue);
    }

    std::vector<Node> caseArgs;
    std::map<Node, Node> caseValues;

    for (std::pair<const Node, UfModelTreeNode>& p : d_data)
    {
      if (!p.first.isNull())
      {
        Node val = p.second.getFunctionValue(args, index + 1, defaultValue);
        caseArgs.push_back(p.first);
        caseValues[p.first] = val;
      }
    }

    NodeManager* nm = NodeManager::currentNM();
    Node retNode = defaultValue;
    // condense function values
    for (size_t i = 0, cargs = caseArgs.size(); i < cargs; i++)
    {
      size_t ii = cargs - i - 1;
      retNode = nm->mkNode(ITE,
                           args[index].eqNode(caseArgs[ii]),
                           caseValues[caseArgs[ii]],
                           retNode);
    }
    return retNode;
  }
  Assert(!d_value.isNull());
  return d_value;
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
    for (auto& kv : d_data)
    {
      if (!kv.first.isNull())
      {
        if (!defaultVal.isNull() && kv.second.d_value == defaultVal)
        {
          eraseData.push_back(kv.first);
        }
        else
        {
          kv.second.simplify(op, defaultVal, argIndex + 1);
          if (kv.second.isEmpty())
          {
            eraseData.push_back(kv.first);
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
    out << m->getRepresentative(d_value);
    out << std::endl;
  }
}

Node UfModelTree::getFunctionValue(const std::vector<Node>& args, Rewriter* r)
{
  Node body = d_tree.getFunctionValue(args, 0, Node::null());
  if (r != nullptr)
  {
    body = r->rewrite(body);
  }
  Node boundVarList = NodeManager::currentNM()->mkNode(kind::BOUND_VAR_LIST, args);
  return NodeManager::currentNM()->mkNode(kind::LAMBDA, boundVarList, body);
}

Node UfModelTree::getFunctionValue(const std::string& argPrefix, Rewriter* r)
{
  TypeNode type = d_op.getType();
  std::vector< Node > vars;
  for( size_t i=0; i<type.getNumChildren()-1; i++ ){
    std::stringstream ss;
    ss << argPrefix << (i+1);
    vars.push_back( NodeManager::currentNM()->mkBoundVar( ss.str(), type[i] ) );
  }
  return getFunctionValue(vars, r);
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

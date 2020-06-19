/*********************                                                        */
/*! \file theory_uf_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model for Theory UF
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY_UF_MODEL_H
#define CVC4__THEORY_UF_MODEL_H

#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {
namespace uf {

class UfModelTreeNode
{
public:
  UfModelTreeNode(){}
  /** the data */
  std::map< Node, UfModelTreeNode > d_data;
  /** the value of this tree node (if all paths lead to same value) */
  Node d_value;
public:
  //is this model tree empty?
  bool isEmpty() { return d_data.empty() && d_value.isNull(); }
  //clear
  void clear();
  /** setValue function */
  void setValue( TheoryModel* m, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex );
  /** getFunctionValue */
  Node getFunctionValue( std::vector< Node >& args, int index, Node argDefaultValue, bool simplify = true );
  /** update function */
  void update( TheoryModel* m );
  /** simplify function */
  void simplify( Node op, Node defaultVal, int argIndex );
  /** is total ? */
  bool isTotal( Node op, int argIndex );
public:
  void debugPrint( std::ostream& out, TheoryModel* m, std::vector< int >& indexOrder, int ind = 0, int arg = 0 );
};

class UfModelTree
{
private:
  //the op this model is for
  Node d_op;
  //the order we will treat the arguments
  std::vector< int > d_index_order;
  //the data
  UfModelTreeNode d_tree;
public:
  //constructors
  UfModelTree(){}
  UfModelTree( Node op ) : d_op( op ){
    TypeNode tn = d_op.getType();
    for( int i=0; i<(int)(tn.getNumChildren()-1); i++ ){
      d_index_order.push_back( i );
    }
  }
  UfModelTree( Node op, std::vector< int >& indexOrder ) : d_op( op ){
    d_index_order.insert( d_index_order.end(), indexOrder.begin(), indexOrder.end() );
  }
  /** clear/reset the function */
  void clear() { d_tree.clear(); }
  /** setValue function
    *
    * For each argument of n with ModelBasisAttribute() set to true will be considered default arguments if ground=false
    *
    */
  void setValue( TheoryModel* m, Node n, Node v, bool ground = true ){
    d_tree.setValue( m, n, v, d_index_order, ground, 0 );
  }
  /** setDefaultValue function */
  void setDefaultValue( TheoryModel* m, Node v ){
    d_tree.setValue( m, Node::null(), v, d_index_order, false, 0 );
  }
  /** getFunctionValue
    *   Returns a representation of this function.
    */
  Node getFunctionValue( std::vector< Node >& args, bool simplify = true );
  /** getFunctionValue for args with set prefix */
  Node getFunctionValue( const char* argPrefix, bool simplify = true );
  /** update
    *   This will update all values in the tree to be representatives in m.
    */
  void update( TheoryModel* m ){ d_tree.update( m ); }
  /** simplify the tree */
  void simplify() { d_tree.simplify( d_op, Node::null(), 0 ); }
  /** is this tree total? */
  bool isTotal() { return d_tree.isTotal( d_op, 0 ); }
  /** is this tree empty? */
  bool isEmpty() { return d_tree.isEmpty(); }
public:
  void debugPrint( std::ostream& out, TheoryModel* m, int ind = 0 ){
    d_tree.debugPrint( out, m, d_index_order, ind );
  }
};

}
}
}

#endif

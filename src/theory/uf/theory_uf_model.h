/*********************                                                        */
/*! \file theory_uf_model.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Model for Theory UF
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_MODEL_H
#define __CVC4__THEORY_UF_MODEL_H

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
  /** has concrete argument defintion */
  bool hasConcreteArgumentDefinition();
public:
  //is this model tree empty?
  bool isEmpty() { return d_data.empty() && d_value.isNull(); }
  //clear
  void clear();
  /** setValue function */
  void setValue( TheoryModel* m, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex );
  /**  getValue function */
  Node getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex );
  Node getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, std::vector< int >& depIndex, int argIndex );
  /** getConstant Value function */
  Node getConstantValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int argIndex );
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
  /**  getValue function
    *
    *  returns val, the value of ground term n
    *  Say n is f( t_0...t_n )
    *    depIndex is the index for which every term of the form f( t_0 ... t_depIndex, *,... * ) is equal to val
    *    for example, if g( x_0, x_1, x_2 ) := lambda x_0 x_1 x_2. if( x_1==a ) b else c,
    *      then g( a, a, a ) would return b with depIndex = 1
    *
    */
  Node getValue( TheoryModel* m, Node n, int& depIndex ){
    return d_tree.getValue( m, n, d_index_order, depIndex, 0 );
  }
  /** -> implementation incomplete */
  Node getValue( TheoryModel* m, Node n, std::vector< int >& depIndex ){
    return d_tree.getValue( m, n, d_index_order, depIndex, 0 );
  }
  /** getConstantValue function
    *
    * given term n, where n may contain "all value" arguments, aka model basis arguments
    *   if n is null, then every argument of n is considered "all value"
    * if n is constant for the entire domain specified by n, then this function returns the value of its domain
    * otherwise, it returns null
    * for example, say the term e represents "all values"
    *   if f( x_0, x_1 ) := if( x_0 = a ) b else if( x_1 = a ) a else b,
    *     then f( a, e ) would return b, while f( e, a ) would return null
    *  -> implementation incomplete
    */
  Node getConstantValue( TheoryModel* m, Node n ) {
    return d_tree.getConstantValue( m, n, d_index_order, 0 );
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
  /** is this function constant? */
  bool isConstant( TheoryModel* m ) { return !getConstantValue( m, Node::null() ).isNull(); }
  /** is this tree empty? */
  bool isEmpty() { return d_tree.isEmpty(); }
public:
  void debugPrint( std::ostream& out, TheoryModel* m, int ind = 0 ){
    d_tree.debugPrint( out, m, d_index_order, ind );
  }
};


class UfModelTreeGenerator
{
public:
  //store for set values
  Node d_default_value;
  std::map< Node, Node > d_set_values[2][2];
  // defaults
  std::vector< Node > d_defaults;
  Node getIntersection( TheoryModel* m, Node n1, Node n2, bool& isGround );
public:
  UfModelTreeGenerator(){}
  ~UfModelTreeGenerator(){}
  /** set default value */
  void setDefaultValue( Node v ) { d_default_value = v; }
  /** set value */
  void setValue( TheoryModel* m, Node n, Node v, bool ground = true, bool isReq = true );
  /** make model */
  void makeModel( TheoryModel* m, UfModelTree& tree );
  /** uses partial default values */
  bool optUsePartialDefaults();
  /** reset */
  void clear();
};

//this class stores temporary information useful to model engine for constructing model
class UfModelPreferenceData
{
public:
  UfModelPreferenceData() : d_reconsiderModel( false ){}
  virtual ~UfModelPreferenceData(){}
  Node d_const_val;
  // preferences for default values
  std::vector< Node > d_values;
  std::map< Node, std::vector< Node > > d_value_pro_con[2];
  std::map< Node, std::vector< Node > > d_term_pro_con[2];
  bool d_reconsiderModel;
  /** set value preference */
  void setValuePreference( Node f, Node n, Node r, bool isPro );
  /** get best default value */
  Node getBestDefaultValue( Node defaultTerm, TheoryModel* m );
};


}
}
}

#endif

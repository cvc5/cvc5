/*********************                                                        */
/*! \file theory_uf_model.h
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
 ** \brief Model for Theory UF
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY_UF_MODEL_H
#define __CVC4__THEORY_UF_MODEL_H

#include "theory/model.h"

namespace CVC4 {
namespace theory {

namespace quantifiers{
  class FirstOrderModel;
}

namespace uf {

class UfModelTree
{
public:
  UfModelTree(){}
  /** the data */
  std::map< Node, UfModelTree > d_data;
  /** the value of this tree node (if all paths lead to same value) */
  Node d_value;
  /** has concrete argument defintion */
  bool hasConcreteArgumentDefinition();
public:
  //is this model tree empty?
  bool isEmpty() { return d_data.empty() && d_value.isNull(); }
  //clear
  void clear();
  /** setValue function
    *
    * For each argument of n with ModelBasisAttribute() set to true will be considered default arguments if ground=false
    *
    */
  void setValue( TheoryModel* m, Node n, Node v, std::vector< int >& indexOrder, bool ground, int argIndex );
  /**  getValue function
    *
    *  returns $val, the value of ground term n
    *  Say n is f( t_0...t_n )
    *    depIndex is the index for which every term of the form f( t_0 ... t_depIndex, *,... * ) is equal to $val
    *    for example, if g( x_0, x_1, x_2 ) := lambda x_0 x_1 x_2. if( x_1==a ) b else c,
    *      then g( a, a, a ) would return b with depIndex = 1
    *  If ground = true, we are asking whether the term n is constant (assumes that all non-model basis arguments are ground)
    *
    */
  Node getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int& depIndex, int argIndex );
  Node getValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, std::vector< int >& depIndex, int argIndex );
  ///** getConstant Value function
  //  *
  //  * given term n, where n may contain model basis arguments
  //  * if n is constant for its entire domain, then this function returns the value of its domain
  //  * otherwise, it returns null
  //  * for example, if f( x_0, x_1 ) := if( x_0 = a ) b else if( x_1 = a ) a else b,
  //  *   then f( a, e ) would return b, while f( e, a ) would return null
  //  *
  //  */
  Node getConstantValue( TheoryModel* m, Node n, std::vector< int >& indexOrder, int argIndex );
  /** getFunctionValue */
  Node getFunctionValue();
  /** simplify function */
  void simplify( Node op, Node defaultVal, int argIndex );
  // is total ?
  bool isTotal( Node op, int argIndex );
public:
  void debugPrint( std::ostream& out, TheoryModel* m, std::vector< int >& indexOrder, int ind = 0, int arg = 0 );
};

class UfModelTreeOrdered
{
private:
  Node d_op;
  std::vector< int > d_index_order;
  UfModelTree d_tree;
public:
  UfModelTreeOrdered(){}
  UfModelTreeOrdered( Node op ) : d_op( op ){
    TypeNode tn = d_op.getType();
    for( int i=0; i<(int)(tn.getNumChildren()-1); i++ ){
      d_index_order.push_back( i );
    }
  }
  UfModelTreeOrdered( Node op, std::vector< int >& indexOrder ) : d_op( op ){
    d_index_order.insert( d_index_order.end(), indexOrder.begin(), indexOrder.end() );
  }
  bool isEmpty() { return d_tree.isEmpty(); }
  void clear() { d_tree.clear(); }
  void setValue( TheoryModel* m, Node n, Node v, bool ground = true ){
    d_tree.setValue( m, n, v, d_index_order, ground, 0 );
  }
  Node getValue( TheoryModel* m, Node n, int& depIndex ){
    return d_tree.getValue( m, n, d_index_order, depIndex, 0 );
  }
  Node getValue( TheoryModel* m, Node n, std::vector< int >& depIndex ){
    return d_tree.getValue( m, n, d_index_order, depIndex, 0 );
  }
  Node getConstantValue( TheoryModel* m, Node n ) {
    return d_tree.getConstantValue( m, n, d_index_order, 0 );
  }
  Node getFunctionValue(){
    return d_tree.getFunctionValue();
  }
  void simplify() { d_tree.simplify( d_op, Node::null(), 0 ); }
  bool isTotal() { return d_tree.isTotal( d_op, 0 ); }
public:
  void debugPrint( std::ostream& out, TheoryModel* m, int ind = 0 ){
    d_tree.debugPrint( out, m, d_index_order, ind );
  }
};

class UfModel
{
private:
  quantifiers::FirstOrderModel* d_model;
  //the operator this model is for
  Node d_op;
  //is model constructed
  bool d_model_constructed;
  //store for set values
  std::map< Node, Node > d_set_values[2][2];
private:
  // defaults
  std::vector< Node > d_defaults;
  Node getIntersection( Node n1, Node n2, bool& isGround );
public:
  UfModel(){}
  UfModel( Node op, quantifiers::FirstOrderModel* m );
  ~UfModel(){}
  //ground terms for this operator
  std::vector< Node > d_ground_asserts;
  //the representatives they are equal to
  std::vector< Node > d_ground_asserts_reps;
  //data structure that stores the model
  UfModelTreeOrdered d_tree;
  //node equivalent of this model
  Node d_func_value;
public:
  /** get operator */
  Node getOperator() { return d_op; }
  /** debug print */
  void toStream( std::ostream& out );
  /** set value */
  void setValue( Node n, Node v, bool ground = true, bool isReq = true );
  /** get value, return arguments that the value depends on */
  Node getValue( Node n, int& depIndex );
  Node getValue( Node n, std::vector< int >& depIndex );
  /** get constant value */
  Node getConstantValue( Node n );
  /** get function value for this function */
  Node getFunctionValue();
  /** is model constructed */
  bool isModelConstructed() { return d_model_constructed; }
  /** is empty */
  bool isEmpty() { return d_ground_asserts.empty(); }
  /** is constant */
  bool isConstant();
  /** uses partial default values */
  bool optUsePartialDefaults();
public:
  /** set model */
  void setModel();
  /** clear model */
  void clearModel();
  /** make model */
  void makeModel( UfModelTreeOrdered& tree );
public:
  /** set value preference */
  void setValuePreference( Node f, Node n, bool isPro );
private:
  //helper for to ITE function.
  static Node toIte2( Node fm_node, std::vector< Node >& args, int index, Node defaultNode );
public:
  /** to ITE function for function model nodes */
  static Node toIte( Node fm_node, std::vector< Node >& args ) { return toIte2( fm_node, args, 0, Node::null() ); }
};

//this class stores temporary information useful to model engine for constructing model
class UfModelPreferenceData
{
public:
  UfModelPreferenceData() : d_reconsiderModel( false ){}
  virtual ~UfModelPreferenceData(){}
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

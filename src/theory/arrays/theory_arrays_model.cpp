/*********************                                                        */
/*! \file theory_arrays_model.cpp
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
 ** \brief Implementation of theory_arrays_model class
 **/

#include "theory/theory_engine.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/term_database.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;

ArrayModel::ArrayModel( Node arr, quantifiers::FirstOrderModel* m ) : d_model( m ), d_arr( arr ){
  Assert( arr.getKind()!=STORE );
  //look at ground assertions
  Node sel = NodeManager::currentNM()->mkNode( SELECT, arr, NodeManager::currentNM()->mkVar( arr.getType().getArrayIndexType() ) );
  Node sel_op = sel.getOperator();  //FIXME: easier way to do this?
  for( size_t i=0; i<d_model->getTermDatabase()->d_op_map[ sel_op ].size(); i++ ){
    Node n = d_model->getTermDatabase()->d_op_map[ sel_op ][i];
    Assert( n.getKind()==SELECT );
    if( m->areEqual( n[0], arr ) ){
      //d_model->getTermDatabase()->computeModelBasisArgAttribute( n );
      //if( !n.getAttribute(NoMatchAttribute()) || n.getAttribute(ModelBasisArgAttribute())==1 ){
        Node r = d_model->getRepresentative( n );
        Node i = d_model->getRepresentative( n[1] );
        d_values[i] = r;
      //}
    }
  }
}

Node ArrayModel::getValue( Node n ){
  Assert( n.getKind()==SELECT );
  Assert( n[0]==d_arr );
  std::map< Node, Node >::iterator it = d_values.find( n[0] );
  if( it!=d_values.end() ){
    return it->second;
  }else{
    return n;
    //return d_default_value;   TODO: guarentee I can return this here
  }
}

void ArrayModel::setDefaultValue( Node v ){
  d_default_value = v;
}

Node ArrayModel::getArrayValue(){
  Node curr = d_arr;    //TODO: make constant default
  for( std::map< Node, Node >::iterator it = d_values.begin(); it != d_values.end(); ++it ){
    curr = NodeManager::currentNM()->mkNode( STORE, curr, it->first, it->second );
  }
  return curr;
}

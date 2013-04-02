/*********************                                                        */
/*! \file theory_arrays_model.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of theory_arrays_model class
 **/

#include "theory/theory_engine.h"
#include "theory/arrays/theory_arrays_model.h"
#include "theory/model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::kind;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::arrays;

ArrayModel::ArrayModel( Node arr, TheoryModel* m ) : d_arr( arr ){
  d_base_arr = arr;
  while( d_base_arr.getKind()==STORE ){
    Node ri = m->getRepresentative( d_base_arr[1] );
    if( d_values.find( ri )==d_values.end() ){
      d_values[ ri ] = m->getRepresentative( d_base_arr[2] );
    }
    d_base_arr = d_base_arr[0];
  }
}

Node ArrayModel::getValue( TheoryModel* m, Node i ){
  i = m->getRepresentative( i );
  std::map< Node, Node >::iterator it = d_values.find( i );
  if( it!=d_values.end() ){
    return it->second;
  }else{
    return NodeManager::currentNM()->mkNode( SELECT, getArrayValue(), i );
    //return d_default_value;   //TODO: guarantee I can return this here
  }
}

void ArrayModel::setValue( TheoryModel* m, Node i, Node e ){
  Node ri = m->getRepresentative( i );
  if( d_values.find( ri )==d_values.end() ){
    d_values[ ri ] = m->getRepresentative( e );
  }
}

void ArrayModel::setDefaultArray( Node arr ){
  d_base_arr = arr;
}

Node ArrayModel::getArrayValue(){
  Node curr = d_base_arr;
  for( std::map< Node, Node >::iterator it = d_values.begin(); it != d_values.end(); ++it ){
    curr = NodeManager::currentNM()->mkNode( STORE, curr, it->first, it->second );
  }
  return curr;
}

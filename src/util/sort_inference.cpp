/*********************                                                        */
/*! \file sort_inference.cpp
 ** \verbatim
 ** Original author: Andrew Reynolds
 ** Major contributors: Morgan Deters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Sort inference module
 **
 ** This class implements sort inference, based on a simple algorithm:
 ** First, we assume all functions and predicates have distinct uninterpreted types.
 ** One pass is made through the input assertions, while a union-find data structure
 ** maintains necessary information regarding constraints on these types.
 **/

#include <vector>

#include "util/sort_inference.h"

using namespace CVC4;
using namespace std;

namespace CVC4 {


void SortInference::printSort( const char* c, int t ){
  int rt = getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    Trace(c) << d_type_types[rt];
  }else{
    Trace(c) << "s_" << rt;
  }
}

void SortInference::simplify( std::vector< Node >& assertions, bool doRewrite ){
  //process all assertions
  for( unsigned i=0; i<assertions.size(); i++ ){
    Trace("sort-inference-debug") << "Process " << assertions[i] << std::endl;
    std::map< Node, Node > var_bound;
    process( assertions[i], var_bound );
  }
  //print debug
  if( Trace.isOn("sort-inference") ){
    for( std::map< Node, int >::iterator it = d_op_return_types.begin(); it != d_op_return_types.end(); ++it ){
      Trace("sort-inference") << it->first << " : ";
      if( !d_op_arg_types[ it->first ].empty() ){
        Trace("sort-inference") << "( ";
        for( size_t i=0; i<d_op_arg_types[ it->first ].size(); i++ ){
          printSort( "sort-inference", d_op_arg_types[ it->first ][i] );
          Trace("sort-inference") << " ";
        }
        Trace("sort-inference") << ") -> ";
      }
      printSort( "sort-inference", it->second );
      Trace("sort-inference") << std::endl;
    }
    for( std::map< Node, std::map< Node, int > >::iterator it = d_var_types.begin(); it != d_var_types.end(); ++it ){
      Trace("sort-inference") << "Quantified formula " << it->first << " : " << std::endl;
      for( std::map< Node, int >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        printSort( "sort-inference", it2->second );
        Trace("sort-inference") << std::endl;
      }
      Trace("sort-inference") << std::endl;
    }
  }
  if( doRewrite ){
    //simplify all assertions by introducing new symbols wherever necessary (NOTE: this is unsound for quantifiers)
    for( unsigned i=0; i<assertions.size(); i++ ){
      std::map< Node, Node > var_bound;
      assertions[i] = simplify( assertions[i], var_bound );
      Trace("sort-inference-rewrite") << " --> " << assertions[i] << std::endl;
    }
    //now, ensure constants are distinct
    for( std::map< TypeNode, std::map< Node, Node > >::iterator it = d_const_map.begin(); it != d_const_map.end(); ++it ){
      std::vector< Node > consts;
      for( std::map< Node, Node >::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2 ){
        consts.push_back( it2->second );
      }
      //add lemma enforcing introduced constants to be distinct?
    }
  }
}

int SortInference::getRepresentative( int t ){
  std::map< int, int >::iterator it = d_type_union_find.find( t );
  if( it!=d_type_union_find.end() ){
    if( it->second==t ){
      return t;
    }else{
      int rt = getRepresentative( it->second );
      d_type_union_find[t] = rt;
      return rt;
    }
  }else{
    return t;
  }
}

void SortInference::setEqual( int t1, int t2 ){
  if( t1!=t2 ){
    int rt1 = getRepresentative( t1 );
    int rt2 = getRepresentative( t2 );
    if( rt1!=rt2 ){
      Trace("sort-inference-debug") << "Set equal : ";
      printSort( "sort-inference-debug", rt1 );
      Trace("sort-inference-debug") << " ";
      printSort( "sort-inference-debug", rt2 );
      Trace("sort-inference-debug") << std::endl;
      //check if they must be a type
      std::map< int, TypeNode >::iterator it1 = d_type_types.find( rt1 );
      std::map< int, TypeNode >::iterator it2 = d_type_types.find( rt2 );
      if( it2!=d_type_types.end() ){
        if( it1==d_type_types.end() ){
          //swap sides
          int swap = rt1;
          rt1 = rt2;
          rt2 = swap;
        }else{
          Assert( rt1==rt2 );
        }
      }
      /*
      d_type_eq_class[rt1].insert( d_type_eq_class[rt1].end(), d_type_eq_class[rt2].begin(), d_type_eq_class[rt2].end() );
      d_type_eq_class[rt2].clear();
      Trace("sort-inference-debug") << "EqClass : { ";
      for( int i=0; i<(int)d_type_eq_class[rt1].size(); i++ ){
        Trace("sort-inference-debug") << d_type_eq_class[rt1][i] << ", ";
      }
      Trace("sort-inference-debug") << "}" << std::endl;
      */
      d_type_union_find[rt2] = rt1;
    }
  }
}

int SortInference::getIdForType( TypeNode tn ){
  //register the return type
  std::map< TypeNode, int >::iterator it = d_id_for_types.find( tn );
  if( it==d_id_for_types.end() ){
    int sc = sortCount;
    d_type_types[ sortCount ] = tn;
    d_id_for_types[ tn ] = sortCount;
    sortCount++;
    return sc;
  }else{
    return it->second;
  }
}

int SortInference::process( Node n, std::map< Node, Node >& var_bound ){
  Trace("sort-inference-debug") << "Process " << n << std::endl;
  //add to variable bindings
  if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
    for( size_t i=0; i<n[0].getNumChildren(); i++ ){
      //TODO: try applying sort inference to quantified variables
      d_var_types[n][ n[0][i] ] = sortCount;
      sortCount++;

      //type of the quantified variable must be the same
      //d_var_types[n][ n[0][i] ] = getIdForType( n[0][i].getType() );
      var_bound[ n[0][i] ] = n;
    }
  }

  //process children
  std::vector< Node > children;
  std::vector< int > child_types;
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    bool processChild = true;
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      processChild = i==1;
    }
    if( processChild ){
      children.push_back( n[i] );
      child_types.push_back( process( n[i], var_bound ) );
    }
  }

  //remove from variable bindings
  if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
    //erase from variable bound
    for( size_t i=0; i<n[0].getNumChildren(); i++ ){
      var_bound.erase( n[0][i] );
    }
  }

  int retType;
  if( n.getKind()==kind::EQUAL ){
    //we only require that the left and right hand side must be equal
    setEqual( child_types[0], child_types[1] );
    retType = getIdForType( n.getType() );
  }else if( n.getKind()==kind::APPLY_UF ){
    Node op = n.getOperator();
    if( d_op_return_types.find( op )==d_op_return_types.end() ){
      //assign arbitrary sort for return type
      d_op_return_types[op] = sortCount;
      sortCount++;
      //d_type_eq_class[sortCount].push_back( op );
      //assign arbitrary sort for argument types
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        d_op_arg_types[op].push_back( sortCount );
        sortCount++;
      }
    }
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      //the argument of the operator must match the return type of the subterm
      setEqual( child_types[i], d_op_arg_types[op][i] );
    }
    //return type is the return type
    retType = d_op_return_types[op];
  }else{
    std::map< Node, Node >::iterator it = var_bound.find( n );
    if( it!=var_bound.end() ){
      Trace("sort-inference-debug") << n << " is a bound variable." << std::endl;
      //the return type was specified while binding
      retType = d_var_types[it->second][n];
    }else if( n.getKind() == kind::VARIABLE ){
      Trace("sort-inference-debug") << n << " is a variable." << std::endl;
      if( d_op_return_types.find( n )==d_op_return_types.end() ){
        //assign arbitrary sort
        d_op_return_types[n] = sortCount;
        sortCount++;
        //d_type_eq_class[sortCount].push_back( n );
      }
      retType = d_op_return_types[n];
    }else if( n.isConst() ){
      Trace("sort-inference-debug") << n << " is a constant." << std::endl;
      //can be any type we want
      retType = sortCount;
      sortCount++;
    }else{
      Trace("sort-inference-debug") << n << " is a interpreted symbol." << std::endl;
      //it is an interpretted term
      for( size_t i=0; i<children.size(); i++ ){
        Trace("sort-inference-debug") << children[i] << " forced to have " << children[i].getType() << std::endl;
        //must enforce the actual type of the operator on the children
        int ct = getIdForType( children[i].getType() );
        setEqual( child_types[i], ct );
      }
      //return type must be the actual return type
      retType = getIdForType( n.getType() );
    }
  }
  Trace("sort-inference-debug") << "Type( " << n << " ) = ";
  printSort("sort-inference-debug", retType );
  Trace("sort-inference-debug") << std::endl;
  return retType;
}


TypeNode SortInference::getOrCreateTypeForId( int t, TypeNode pref ){
  int rt = getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    return d_type_types[rt];
  }else{
    TypeNode retType;
    //see if we can assign pref
    if( !pref.isNull() && d_id_for_types.find( pref )==d_id_for_types.end() ){
      retType = pref;
    }else{
      if( d_subtype_count.find( pref )==d_subtype_count.end() ){
        d_subtype_count[pref] = 0;
      }
      //must create new type
      std::stringstream ss;
      ss << "it_" << d_subtype_count[pref] << "_" << pref;
      d_subtype_count[pref]++;
      retType = NodeManager::currentNM()->mkSort( ss.str() );
    }
    d_id_for_types[ retType ] = rt;
    d_type_types[ rt ] = retType;
    return retType;
  }
}

TypeNode SortInference::getTypeForId( int t ){
  int rt = getRepresentative( t );
  if( d_type_types.find( rt )!=d_type_types.end() ){
    return d_type_types[rt];
  }else{
    return TypeNode::null();
  }
}

Node SortInference::getNewSymbol( Node old, TypeNode tn ){
  if( tn==old.getType() ){
    return old;
  }else if( old.isConst() ){
    //must make constant of type tn
    if( d_const_map[tn].find( old )==d_const_map[tn].end() ){
      std::stringstream ss;
      ss << "ic_" << tn << "_" << old;
      d_const_map[tn][ old ] = NodeManager::currentNM()->mkSkolem( ss.str(), tn, "constant created during sort inference" );  //use mkConst???
    }
    return d_const_map[tn][ old ];
  }else{
    std::stringstream ss;
    ss << "i_$$_" << old;
    return NodeManager::currentNM()->mkSkolem( ss.str(), tn, "created during sort inference" );
  }
}

Node SortInference::simplify( Node n, std::map< Node, Node >& var_bound ){
  std::vector< Node > children;
  if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
    //recreate based on types of variables
    std::vector< Node > new_children;
    for( size_t i=0; i<n[0].getNumChildren(); i++ ){
      TypeNode tn = getOrCreateTypeForId( d_var_types[n][ n[0][i] ], n[0][i].getType() );
      Node v = getNewSymbol( n[0][i], tn );
      new_children.push_back( v );
      var_bound[ n[0][i] ] = v;
    }
    children.push_back( NodeManager::currentNM()->mkNode( n[0].getKind(), new_children ) );
  }

  //process children
  if( n.getMetaKind() == kind::metakind::PARAMETERIZED ){
    children.push_back( n.getOperator() );
  }
  for( size_t i=0; i<n.getNumChildren(); i++ ){
    bool processChild = true;
    if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
      processChild = i>=1;
    }
    if( processChild ){
      children.push_back( simplify( n[i], var_bound ) );
    }
  }

  //remove from variable bindings
  if( n.getKind()==kind::FORALL || n.getKind()==kind::EXISTS ){
    //erase from variable bound
    for( size_t i=0; i<n[0].getNumChildren(); i++ ){
      var_bound.erase( n[0][i] );
    }
    return NodeManager::currentNM()->mkNode( n.getKind(), children );
  }else if( n.getKind()==kind::EQUAL ){
    if( children[0].getType()!=children[1].getType() ){
      if( children[0].isConst() ){
        children[0] = getNewSymbol( children[0], children[1].getType() );
      }else if( children[1].isConst() ){
        children[1] = getNewSymbol( children[1], children[0].getType() );
      }else{
        Trace("sort-inference-warn") << "Sort inference created bad equality: " << children[0] << " = " << children[1] << std::endl;
        Trace("sort-inference-warn") << "  Types : " << children[0].getType() << " " << children[1].getType() << std::endl;
        Assert( false );
      }
    }
    return NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
  }else if( n.getKind()==kind::APPLY_UF ){
    Node op = n.getOperator();
    if( d_symbol_map.find( op )==d_symbol_map.end() ){
      //make the new operator if necessary
      bool opChanged = false;
      std::vector< TypeNode > argTypes;
      for( size_t i=0; i<n.getNumChildren(); i++ ){
        TypeNode tn = getOrCreateTypeForId( d_op_arg_types[op][i], n[i].getType() );
        argTypes.push_back( tn );
        if( tn!=n[i].getType() ){
          opChanged = true;
        }
      }
      TypeNode retType = getOrCreateTypeForId( d_op_return_types[op], n.getType() );
      if( retType!=n.getType() ){
        opChanged = true;
      }
      if( opChanged ){
        std::stringstream ss;
        ss << "io_$$_" << op;
        TypeNode typ = NodeManager::currentNM()->mkFunctionType( argTypes, retType );
        d_symbol_map[op] = NodeManager::currentNM()->mkSkolem( ss.str(), typ, "op created during sort inference" );
      }else{
        d_symbol_map[op] = op;
      }
    }
    children[0] = d_symbol_map[op];
    //make sure all children have been taken care of
    for( size_t i=0; i<n.getNumChildren(); i++ ){
      TypeNode tn = children[i+1].getType();
      TypeNode tna = getTypeForId( d_op_arg_types[op][i] );
      if( tn!=tna ){
        if( n[i].isConst() ){
          children[i+1] = getNewSymbol( n[i], tna );
        }else{
          Trace("sort-inference-warn") << "Sort inference created bad child: " << n[i] << " " << tn << " " << tna << std::endl;
          Assert( false );
        }
      }
    }
    return NodeManager::currentNM()->mkNode( kind::APPLY_UF, children );
  }else{
    std::map< Node, Node >::iterator it = var_bound.find( n );
    if( it!=var_bound.end() ){
      return it->second;
    }else if( n.getKind() == kind::VARIABLE ){
      if( d_symbol_map.find( n )==d_symbol_map.end() ){
        TypeNode tn = getOrCreateTypeForId( d_op_return_types[n], n.getType() );
        d_symbol_map[n] = getNewSymbol( n, tn );
      }
      return d_symbol_map[n];
    }else if( n.isConst() ){
      //just return n, we will fix at higher scope
      return n;
    }else{
      return NodeManager::currentNM()->mkNode( n.getKind(), children );
    }
  }

}
int SortInference::getSortId( Node n ) {
  Node op = n.getKind()==kind::APPLY_UF ? n.getOperator() : n;
  return getRepresentative( d_op_return_types[op] );
}

int SortInference::getSortId( Node f, Node v ) {
  return getRepresentative( d_var_types[f][v] );
}

void SortInference::setSkolemVar( Node f, Node v, Node sk ){
  d_op_return_types[sk] = getSortId( f, v );
}

}/* CVC4 namespace */

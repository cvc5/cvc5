/*********************                                                        */
/*! \file rels_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory implementation.
 **
 ** Extension to Sets theory.
 **/

#ifndef SRC_THEORY_SETS_RELS_UTILS_H_
#define SRC_THEORY_SETS_RELS_UTILS_H_

#include "expr/dtype.h"
#include "expr/node.h"

namespace CVC4 {
namespace theory {
namespace sets {

class RelsUtils {

public:

  // Assumption: the input rel_mem contains all constant pairs
  static std::set< Node > computeTC( std::set< Node > rel_mem, Node rel ) {
    std::set< Node >::iterator mem_it = rel_mem.begin();
    std::map< Node, int > ele_num_map;
    std::set< Node > tc_rel_mem;
       
    while( mem_it != rel_mem.end() ) {
      Node fst = nthElementOfTuple( *mem_it, 0 );
      Node snd = nthElementOfTuple( *mem_it, 1 );
      std::set< Node > traversed;
      traversed.insert(fst);
      computeTC(rel, rel_mem, fst, snd, traversed, tc_rel_mem);      
      mem_it++;             
    }
    return tc_rel_mem;
  }
  
  static void computeTC( Node rel, std::set< Node >& rel_mem, Node fst, 
                         Node snd, std::set< Node >& traversed, std::set< Node >& tc_rel_mem ) {    
    tc_rel_mem.insert(constructPair(rel, fst, snd));
    if( traversed.find(snd) == traversed.end() ) {
      traversed.insert(snd);
    } else {
      return;
    }

    std::set< Node >::iterator mem_it = rel_mem.begin();
    while( mem_it != rel_mem.end() ) {
      Node new_fst = nthElementOfTuple( *mem_it, 0 );
      Node new_snd = nthElementOfTuple( *mem_it, 1 );
      if( snd == new_fst ) {
        computeTC(rel, rel_mem, fst, new_snd, traversed, tc_rel_mem);
      }
      mem_it++; 
    }  
  }
 
  static Node nthElementOfTuple( Node tuple, int n_th ) {    
    if( tuple.getKind() == kind::APPLY_CONSTRUCTOR ) {
      return tuple[n_th];
    }
    TypeNode tn = tuple.getType();
    const DType& dt = tn.getDType();
    return NodeManager::currentNM()->mkNode(
        kind::APPLY_SELECTOR_TOTAL, dt[0].getSelectorInternal(tn, n_th), tuple);
  } 
  
  static Node reverseTuple( Node tuple ) {
    Assert(tuple.getType().isTuple());
    std::vector<Node> elements;
    std::vector<TypeNode> tuple_types = tuple.getType().getTupleTypes();
    std::reverse( tuple_types.begin(), tuple_types.end() );
    TypeNode tn = NodeManager::currentNM()->mkTupleType( tuple_types );
    const DType& dt = tn.getDType();
    elements.push_back(dt[0].getConstructor());
    for(int i = tuple_types.size() - 1; i >= 0; --i) {
      elements.push_back( nthElementOfTuple(tuple, i) );
    }
    return NodeManager::currentNM()->mkNode( kind::APPLY_CONSTRUCTOR, elements );
  }
  static Node constructPair(Node rel, Node a, Node b) {
    const DType& dt = rel.getType().getSetElementType().getDType();
    return NodeManager::currentNM()->mkNode(
        kind::APPLY_CONSTRUCTOR, dt[0].getConstructor(), a, b);
  }     
    
};             
}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif

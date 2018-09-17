/*********************                                                        */
/*! \file node_trie.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of node trie.
 **/

#include "expr/node_trie.h"

namespace CVC4 {
namespace theory {
  

TNode TNodeTrie::existsTerm( std::vector< TNode >& reps ) {
  TNodeTrie * tnt = this;
  for( TNode r : reps )
  {
    std::map< TNode, TNodeTrie >::iterator it = tnt->d_data.find( r );
    if( it==d_data.end() ){
      // didn't find this child, return null
      return Node::null();
    }
    tnt = &it->second;
  }
  if( d_data.empty() ){
    return Node::null();
  }
  return d_data.begin()->first;
}

bool TNodeTrie::addTerm( TNode n, std::vector< TNode >& reps ){
  return addOrGetTerm( n, reps )==n;
}

TNode TNodeTrie::addOrGetTerm( TNode n, std::vector< TNode >& reps ) {
  TNodeTrie * tnt = this;
  for( TNode r : reps )
  {
    tnt = &(tnt->d_data[r]);
  }
  if( tnt->d_data.empty() ){
    // Store n in d_data. This should be interpretted as the "data" and not as a
    // reference to a child.
    tnt->d_data[n].clear();
    return n;
  }
  return tnt->d_data.begin()->first;
}

void TNodeTrie::debugPrint( const char * c, Node n, unsigned depth ) {
  for( std::pair< const TNode, TNodeTrie >& p : d_data )
  {
    for( unsigned i=0; i<depth; i++ ){ 
      Trace(c) << "  ";
    }
    Trace(c) << p.first << std::endl;
    p.second.debugPrint( c, n, depth+1 );
  }
}

} /* CVC4::theory namespace */
} /* CVC4 namespace */

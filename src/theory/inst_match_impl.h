/*********************                                                        */
/*! \file inst_match_impl.h
 ** \verbatim
 ** Original author: bobot
 ** Major contributors: none
 ** Minor contributors (to current version): taking, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__INST_MATCH_IMPL_H
#define __CVC4__INST_MATCH_IMPL_H

#include "theory/inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/uf/theory_uf_instantiator.h"
#include "theory/uf/theory_uf_candidate_generator.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {

template<bool modEq>
InstMatchTrie2<modEq>::InstMatchTrie2(context::Context* c,  QuantifiersEngine* qe):
  d_data(c->getLevel()), d_context(c), d_mods(c) {
  d_eQ = qe->getEqualityQuery();
  d_eE = ((uf::TheoryUF*)qe->getTheoryEngine()->getTheory( THEORY_UF ))->getEqualityEngine();
};

/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
template<bool modEq>
void InstMatchTrie2<modEq>::addSubTree( Tree * root, mapIter current, mapIter end, size_t currLevel ) {
  if( current == end ) return;

  Assert(root->e.find(current->second) == root->e.end());
  Tree * root2 = new Tree(currLevel);
  root->e.insert(std::make_pair(current->second, root2));
  addSubTree(root2, ++current, end, currLevel );
}

/** exists match */
template<bool modEq>
bool InstMatchTrie2<modEq>::existsInstMatch(InstMatchTrie2<modEq>::Tree * root,
                                            mapIter & current, mapIter & end,
                                            Tree * & e, mapIter & diverge) const{
  if( current == end ) {
    Debug("Trie2") << "Trie2 Bottom " << std::endl;
    --current;
    return true;
  }; //Already their

  if (current->first > diverge->first){
    // this point is the deepest point currently seen map are ordered
    e = root;
    diverge = current;
  };

  TNode n = current->second;
  typename InstMatchTrie2<modEq>::Tree::MLevel::iterator it =
    root->e.find( n );
  if( it!=root->e.end() &&
      existsInstMatch( (*it).second, ++current, end, e, diverge) ){
    Debug("Trie2") << "Trie2 Directly here " << n << std::endl;
    --current;
    return true;
  }
  Assert( it==root->e.end() || e != root );

  // Even if n is in the trie others of the equivalence class
  // can also be in it since the equality can have appeared
  // after they have been added
  if( modEq && d_eE->hasTerm( n ) ){
    //check modulo equality if any other instantiation match exists
    eq::EqClassIterator eqc( d_eQ->getRepresentative( n ), d_eE );
    for( ;!eqc.isFinished();++eqc ){
      TNode en = (*eqc);
      if( en == n ) continue; // already tested
      typename InstMatchTrie2<modEq>::Tree::MLevel::iterator itc =
        root->e.find( en );
      if( itc!=root->e.end() &&
          existsInstMatch( (*itc).second, ++current, end, e, diverge) ){
        Debug("Trie2") << "Trie2 Indirectly here by equality " << n << " = " << en << std::endl;
        --current;
        return true;
      }
      Assert( itc==root->e.end() || e != root );
    }
  }
  --current;
  return false;
}

template<bool modEq>
bool InstMatchTrie2<modEq>::addInstMatch( InstMatch& m ) {
 mapIter begin = m.d_map.begin();
 mapIter end = m.d_map.end();
 typename InstMatchTrie2<modEq>::Tree * e = &d_data;
 mapIter diverge = begin;
 if( !existsInstMatch(e, begin, end, e, diverge ) ){
   Assert(!diverge->second.isNull());
   size_t currLevel = d_context->getLevel();
   addSubTree( e, diverge, end, currLevel );
   if(e->level != currLevel)
     //If same level that e, will be removed at the same time than e
     d_mods.push_back(std::make_pair(e,diverge->second));
   return true;
 }else{
   return false;
 }
}

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /*  __CVC4__INST_MATCH_IMPL_H */

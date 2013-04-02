/*********************                                                        */
/*! \file rr_inst_match_impl.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Francois Bobot
 ** Minor contributors (to current version): Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief inst match class
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_IMPL_H
#define __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_IMPL_H

#include "theory/rewriterules/rr_inst_match.h"
#include "theory/theory_engine.h"
#include "theory/quantifiers_engine.h"
#include "theory/rewriterules/rr_candidate_generator.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace rrinst {

template<bool modEq>
InstMatchTrie2Gen<modEq>::InstMatchTrie2Gen(context::Context* c,  QuantifiersEngine* qe):
  d_context(c), d_mods(c) {
  d_eQ = qe->getEqualityQuery();
  d_cG = new GenericCandidateGeneratorClass(qe);
};

/** add match m for quantifier f starting at index, take into account equalities q, return true if successful */
template<bool modEq>
void InstMatchTrie2Gen<modEq>::addSubTree( Tree * root, mapIter current, mapIter end, size_t currLevel ) {
  if( current == end ) return;

  Assert(root->e.find(current->second) == root->e.end());
  Tree * root2 = new Tree(currLevel);
  root->e.insert(std::make_pair(current->second, root2));
  addSubTree(root2, ++current, end, currLevel );
}

/** exists match */
template<bool modEq>
bool InstMatchTrie2Gen<modEq>::existsInstMatch(InstMatchTrie2Gen<modEq>::Tree * root,
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
  typename InstMatchTrie2Gen<modEq>::Tree::MLevel::iterator it =
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
  if( modEq && d_eQ->hasTerm( n ) ){
    //check modulo equality if any other instantiation match exists
    d_cG->reset( d_eQ->getRepresentative( n ) );
    for(TNode en = d_cG->getNextCandidate() ; !en.isNull() ;
        en = d_cG->getNextCandidate() ){
      if( en == n ) continue; // already tested
      typename InstMatchTrie2Gen<modEq>::Tree::MLevel::iterator itc =
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
bool InstMatchTrie2Gen<modEq>::
addInstMatch( InstMatch& m, InstMatchTrie2Gen<modEq>::Tree* e ) {
  d_cG->resetInstantiationRound();
 mapIter begin = m.begin();
 mapIter end = m.end();
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

}/* CVC4::theory::rrinst namespace */

}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /*  __CVC4__THEORY__REWRITERULES__RR_INST_MATCH_IMPL_H */

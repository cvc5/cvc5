/*********************                                                        */
/*! \file bvintropow2.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/bvintropow2.h"
#include "theory/rewriter.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"


namespace CVC4 {
namespace theory {
namespace bv {

void BVIntroducePow2::pow2Rewrite(std::vector<Node>& assertionsToPreprocess){
  NodeMap cache;
  for(size_t i = 0, N= assertionsToPreprocess.size(); i < N; ++i){
    Node curr = assertionsToPreprocess[i];
    Node next = pow2Rewrite(curr, cache);
    if(next != curr){
      Node tmp = Rewriter::rewrite(next);
      next = tmp;
    }
    assertionsToPreprocess[i] = next;
  }
}

Node  BVIntroducePow2::pow2Rewrite(Node node, NodeMap& cache){
  NodeMap::const_iterator ci = cache.find(node);
  if(ci != cache.end()){
    Node incache = (*ci).second;
    
    return incache.isNull() ? node : incache;
  }

  Node res = Node::null();
  switch(node.getKind()){
  case kind::AND:
    {
      bool changed = false;
      std::vector<Node> children;
      for(unsigned i = 0, N = node.getNumChildren(); i < N; ++i){
        Node child = node[i];
        Node found = pow2Rewrite(child, cache);
        changed = changed || (child != found);
        children.push_back(found);
      }
      if(changed){
        res = NodeManager::currentNM()->mkNode(kind::AND, children);
      }
    }
    break;

  case kind::EQUAL:
    if(node[0].getType().isBitVector()){
      if (RewriteRule<IsPowerOfTwo>::applies(node)) {
        res = RewriteRule<IsPowerOfTwo>::run<false>(node);
      }
    }
    break;
  default:
    break;
  }

  cache.insert(std::make_pair(node, res));
  return res.isNull() ? node : res;
}


}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

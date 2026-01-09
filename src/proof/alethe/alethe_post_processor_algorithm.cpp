/******************************************************************************
 * Top contributors (to current version):
 *   Hanna Lachnitt, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Algorithms used by the Alethe post processor
 */

#include "expr/nary_term_util.h"
#include "proof/alethe/alethe_post_processor.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

namespace proof {

//Naive implementation, probably want to implement caching at some point
Node applyAcSimp(std::map<Node,Node>& cache, Node term){ 
  if (cache.find(term) != cache.end()){
     return cache[term];
  }
  Kind k = term.getKind();
  Node result;
  //std::cout << "term: " << term << " kind " << k << std::endl;
  if (term.getMetaKind() == metakind::PARAMETERIZED){
    //not supported
    return term;
  }
  std::vector<Node> new_children;
  if (k == Kind::AND || k == Kind::OR){
    for (Node child : term){
       Node new_term = applyAcSimp(cache, child);
       Kind k_new_term = new_term.getKind();
       if (k_new_term == k){
         for (Node c : new_term){
           if (std::find(new_children.begin(), new_children.end(), c) == new_children.end()){
	      new_children.push_back(c);
	   }
         }
       }
       else {
          if (std::find(new_children.begin(), new_children.end(), new_term) == new_children.end()){
	      new_children.push_back(new_term);
	   }
       } 
    }
    if (new_children.size() == 1){
      return new_children[0];
    }
    else {
      result = NodeManager::currentNM()->mkNode(k, new_children);
    }
  }
  else if (term.getNumChildren() == 0){
    return term;
  }
  else { 
    for (Node child : term){ 
      Node new_term = applyAcSimp(cache, child);
        new_children.push_back(new_term);
      
    }
    if (k == Kind::APPLY_UF){
      new_children.insert(new_children.begin(),term.getOperator());
    }
    result = NodeManager::currentNM()->mkNode(k,new_children);
  }
  cache.insert({term,result});
  return result;
}

}  // namespace proof
}  // namespace cvc5::internal


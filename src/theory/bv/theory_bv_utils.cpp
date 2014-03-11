/*********************                                                        */
/*! \file theory_bv_utils.h
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Liana Hadarean
 ** Minor contributors (to current version): Clark Barrett, Morgan Deters, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/bv/theory_bv_utils.h"
#include "theory/decision_attributes.h"
#include "theory/theory.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

bool CVC4::theory::bv::utils::isCoreTerm(TNode term, TNodeBoolMap& cache) {
  term = term.getKind() == kind::NOT ? term[0] : term; 
  TNodeBoolMap::const_iterator it = cache.find(term); 
  if (it != cache.end()) {
    return it->second;
  }
    
  if (term.getNumChildren() == 0)
    return true;
  
  if (theory::Theory::theoryOf(term) == THEORY_BV) {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR &&
        k != kind::BITVECTOR_CONCAT &&
        k != kind::BITVECTOR_EXTRACT &&
        k != kind::EQUAL) {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    if (!isCoreTerm(term[i], cache)) {
      cache[term] = false;
      return false;
    }
  }
  
  cache[term]= true; 
  return true;
}

uint64_t CVC4::theory::bv::utils::numNodes(TNode node, NodeSet& seen) {
  if (seen.find(node) != seen.end())
    return 0;

  uint64_t size = 1;
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    size += numNodes(node[i], seen);
  }
  seen.insert(node);
  return size;
}

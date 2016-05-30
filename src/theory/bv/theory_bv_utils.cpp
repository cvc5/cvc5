/*********************                                                        */
/*! \file theory_bv_utils.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Tim King
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

#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace bv {
namespace utils {

bool isCoreTerm(TNode term, TNodeBoolMap& cache) {
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end()) {
    return it->second;
  }

  if (term.getNumChildren() == 0)
    return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV) {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR &&
        k != kind::BITVECTOR_CONCAT &&
        k != kind::BITVECTOR_EXTRACT &&
        k != kind::EQUAL &&
        term.getMetaKind() != kind::metakind::VARIABLE) {
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

bool isEqualityTerm(TNode term, TNodeBoolMap& cache) {
  term = term.getKind() == kind::NOT ? term[0] : term;
  TNodeBoolMap::const_iterator it = cache.find(term);
  if (it != cache.end()) {
    return it->second;
  }

  if (term.getNumChildren() == 0)
    return true;

  if (theory::Theory::theoryOf(theory::THEORY_OF_TERM_BASED, term) == THEORY_BV) {
    Kind k = term.getKind();
    if (k != kind::CONST_BITVECTOR &&
        k != kind::EQUAL &&
        term.getMetaKind() != kind::metakind::VARIABLE) {
      cache[term] = false;
      return false;
    }
  }

  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    if (!isEqualityTerm(term[i], cache)) {
      cache[term] = false;
      return false;
    }
  }

  cache[term]= true;
  return true;
}


uint64_t numNodes(TNode node, NodeSet& seen) {
  if (seen.find(node) != seen.end())
    return 0;

  uint64_t size = 1;
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    size += numNodes(node[i], seen);
  }
  seen.insert(node);
  return size;
}

void collectVariables(TNode node, NodeSet& vars) {
  if (vars.find(node) != vars.end())
    return;

  if (Theory::isLeafOf(node, THEORY_BV) && node.getKind() != kind::CONST_BITVECTOR) {
    vars.insert(node);
    return;
  }
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    collectVariables(node[i], vars);
  }
}

}/* CVC4::theory::bv::utils namespace */
}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

/*********************                                                        */
/*! \file theory_bv_rewrite_rules_normalization.h
 ** \verbatim
 ** Original author: lianah
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#pragma once

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

/**
 * ExtractBitwise
 *   (x bvop y) [i:j] ==> x[i:j] bvop y[i:j]
 *  where bvop is bvand,bvor, bvxor
 */
template<>
bool RewriteRule<ExtractBitwise>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_AND ||
           node[0].getKind() == kind::BITVECTOR_OR ||
           node[0].getKind() == kind::BITVECTOR_XOR ));
}

template<>
Node RewriteRule<ExtractBitwise>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractBitwise>(" << node << ")" << std::endl;
  unsigned high = utils::getExtractHigh(node);
  unsigned low = utils::getExtractLow(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  Node b = utils::mkExtract(node[0][1], high, low);
  Kind kind = node[0].getKind(); 
  return utils::mkNode(kind, a, b);
}

/**
 * ExtractNot
 *
 *  (~ a) [i:j] ==> ~ (a[i:j])
 */
template<>
bool RewriteRule<ExtractNot>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getKind() == kind::BITVECTOR_NOT);
}

template<>
Node RewriteRule<ExtractNot>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractNot>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  return utils::mkNode(kind::BITVECTOR_NOT, a); 
}

/**
 * ExtractArith
 * 
 * (a bvop b) [k:0] ==> (a[k:0] bvop b[k:0])
 */

template<>
bool RewriteRule<ExtractArith>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::getExtractLow(node) == 0 &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<>
Node RewriteRule<ExtractArith>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractArith>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  Assert (low == 0); 
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  Node b = utils::mkExtract(node[0][1], high, low);
  
  Kind kind = node[0].getKind(); 
  return utils::mkNode(kind, a, b); 
  
}

/**
 * ExtractArith2
 *
 * (a bvop b) [i:j] ==> (a[i:0] bvop b[i:0]) [i:j]
 */

// careful not to apply in a loop 
template<>
bool RewriteRule<ExtractArith2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<>
Node RewriteRule<ExtractArith2>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<ExtractArith2>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, 0);
  Node b = utils::mkExtract(node[0][1], high, 0);
  
  Kind kind = node[0].getKind(); 
  Node a_op_b = utils::mkNode(kind, a, b); 
  
  return utils::mkExtract(a_op_b, high, low); 
}


// template<>
// bool RewriteRule<>::applies(Node node) {
//   return (node.getKind() == kind::BITVECTOR_CONCAT);
// }

// template<>
// Node RewriteRule<>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return resultNode;
// }



}
}
}

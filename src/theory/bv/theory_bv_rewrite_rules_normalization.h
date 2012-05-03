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
template<> inline
bool RewriteRule<ExtractBitwise>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_AND ||
           node[0].getKind() == kind::BITVECTOR_OR ||
           node[0].getKind() == kind::BITVECTOR_XOR ));
}

template<> inline
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
template<> inline
bool RewriteRule<ExtractNot>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getKind() == kind::BITVECTOR_NOT);
}

template<> inline
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

template<> inline
bool RewriteRule<ExtractArith>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::getExtractLow(node) == 0 &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<> inline
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
template<> inline
bool RewriteRule<ExtractArith2>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<> inline
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

template<> inline
bool RewriteRule<FlattenAssocCommut>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_PLUS ||
          node.getKind() == kind::BITVECTOR_MULT ||
          node.getKind() == kind::BITVECTOR_OR ||
          node.getKind() == kind::BITVECTOR_XOR ||
          node.getKind() == kind::BITVECTOR_AND);
}


template<> inline
Node RewriteRule<FlattenAssocCommut>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")" << std::endl;
  std::vector<Node> processingStack;
  processingStack.push_back(node);
  std::vector<Node> children;
  Kind kind = node.getKind(); 
  
  while (! processingStack.empty()) {
    TNode current = processingStack.back();
    processingStack.pop_back();

    // flatten expression
    if (current.getKind() == kind) {
      for (unsigned i = 0; i < current.getNumChildren(); ++i) {
        processingStack.push_back(current[i]);
      }
    } else {
      children.push_back(current); 
    }
  }
  return utils::mkSortedNode(kind, children); 
}

static inline void addToCoefMap(std::map<Node, BitVector>& map,
                                TNode term, const BitVector& coef) {
  if (map.find(term) != map.end()) {
    map[term] = map[term] + coef; 
  } else {
    map[term] = coef;
  }
}


template<> inline
bool RewriteRule<PlusCombineLikeTerms>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_PLUS);
}

template<> inline
Node RewriteRule<PlusCombineLikeTerms>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<PlusCombineLikeTerms>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constSum(size, (unsigned)0); 
  std::map<Node, BitVector> factorToCoefficient;

  // combine like-terms
  for(unsigned i= 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    
    // look for c * x, where c is a constant
    if (current.getKind() == kind::BITVECTOR_MULT &&
        (current[0].getKind() == kind::CONST_BITVECTOR ||
         current[1].getKind() == kind::CONST_BITVECTOR)) {
      // if we are multiplying by a constant
      BitVector coeff;
      TNode term;
      // figure out which part is the constant
      if (current[0].getKind() == kind::CONST_BITVECTOR) {
        coeff = current[0].getConst<BitVector>();
        term = current[1];
      } else {
        coeff = current[1].getConst<BitVector>();
        term = current[0];
      }
      if(term.getKind() == kind::BITVECTOR_SUB) {
        TNode a = term[0];
        TNode b = term[1];
        addToCoefMap(factorToCoefficient, a, coeff);
        addToCoefMap(factorToCoefficient, b, -coeff); 
      }
      else if(term.getKind() == kind::BITVECTOR_NEG) {
        addToCoefMap(factorToCoefficient, term[0], -BitVector(size, coeff));
      }
      else {
        addToCoefMap(factorToCoefficient, term, coeff);
      }
    }
    else if (current.getKind() == kind::BITVECTOR_SUB) {
      // turn into a + (-1)*b 
      addToCoefMap(factorToCoefficient, current[0], BitVector(size, (unsigned)1)); 
      addToCoefMap(factorToCoefficient, current[1], -BitVector(size, (unsigned)1)); 
    }
    else if (current.getKind() == kind::BITVECTOR_NEG) {
      addToCoefMap(factorToCoefficient, current[0], -BitVector(size, (unsigned)1)); 
    }
    else if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector constValue = current.getConst<BitVector>(); 
      constSum = constSum + constValue;
    }
    else {
      // store as 1 * current
      addToCoefMap(factorToCoefficient, current, BitVector(size, (unsigned)1)); 
    }
  }
    
  std::vector<Node> children; 
  if ( constSum!= BitVector(size, (unsigned)0)) {
    children.push_back(utils::mkConst(constSum)); 
  }

  // construct result 
  std::map<Node, BitVector>::const_iterator it = factorToCoefficient.begin();
  
  for (; it != factorToCoefficient.end(); ++it) {
    BitVector bv_coeff = it->second;
    TNode term = it->first;
    if(bv_coeff == BitVector(size, (unsigned)0)) {
      continue;
    }
    else if (bv_coeff == BitVector(size, (unsigned)1)) {
      children.push_back(term); 
    }
    else if (bv_coeff == -BitVector(size, (unsigned)1)) {
      // avoid introducing an extra multiplication
      children.push_back(utils::mkNode(kind::BITVECTOR_NEG, term)); 
    }
    else {
      Node coeff = utils::mkConst(bv_coeff);
      Node product = utils::mkSortedNode(kind::BITVECTOR_MULT, coeff, term); 
      children.push_back(product); 
    }
  }

  if(children.size() == 0) {
    return utils::mkConst(size, (unsigned)0); 
  }
  
  return utils::mkSortedNode(kind::BITVECTOR_PLUS, children);
}


template<> inline
bool RewriteRule<MultSimplify>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_MULT);
}

template<> inline
Node RewriteRule<MultSimplify>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultSimplify>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constant(size, Integer(1));

  std::vector<Node> children; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector value = current.getConst<BitVector>();
      if(value == BitVector(size, (unsigned) 0)) {
        return utils::mkConst(size, 0); 
      }
      constant = constant * current.getConst<BitVector>();
    } else {
      children.push_back(current); 
    }
  }


  if(constant != BitVector(size, (unsigned)1)) {
    children.push_back(utils::mkConst(constant)); 
  }

  
  if(children.size() == 0) {
    return utils::mkConst(size, (unsigned)1); 
  }

  return utils::mkSortedNode(kind::BITVECTOR_MULT, children); 
}

template<> inline
bool RewriteRule<MultDistribConst>::applies(Node node) {
  if (node.getKind() != kind::BITVECTOR_MULT)
    return false;

  TNode factor;
  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    factor = node[1];
  } else if (node[1].getKind() == kind::CONST_BITVECTOR) {
    factor = node[0];
  } else {
    return false; 
  }
  
  return (factor.getKind() == kind::BITVECTOR_PLUS ||
          factor.getKind() == kind::BITVECTOR_SUB ||
          factor.getKind() == kind::BITVECTOR_NEG); 
}

template<> inline
Node RewriteRule<MultDistribConst>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<MultDistribConst>(" << node << ")" << std::endl;

  TNode constant;
  TNode factor;
  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    constant = node[0];
    factor = node[1]; 
  } else {
  Assert(node[1].getKind() == kind::CONST_BITVECTOR);
  constant = node[1];
  factor = node[0];
  }

  if (factor.getKind() == kind::BITVECTOR_NEG) {
    // push negation on the constant part
    BitVector const_bv = constant.getConst<BitVector>();
    return utils::mkSortedNode(kind::BITVECTOR_MULT,
                               utils::mkConst(-const_bv),
                               factor[0]); 
  }

  std::vector<Node> children;
  for(unsigned i = 0; i < factor.getNumChildren(); ++i) {
    children.push_back(utils::mkSortedNode(kind::BITVECTOR_MULT, constant, factor[i])); 
  }
  
  return utils::mkSortedNode(factor.getKind(), children); 
                              
}


/**
 * -(c * expr) ==> (-c * expr)
 * where c is a constant
 */
template<> inline
bool RewriteRule<NegMult>::applies(Node node) {
  if(node.getKind()!= kind::BITVECTOR_NEG ||
     node[0].getKind() != kind::BITVECTOR_MULT) {
    return false; 
  }
  TNode mult = node[0]; 
  for (unsigned i = 0; i < mult.getNumChildren(); ++i) {
    if (mult[i].getKind() == kind::CONST_BITVECTOR) {
      return true; 
    }
  } 
  return false; 
}

template<> inline
Node RewriteRule<NegMult>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegMult>(" << node << ")" << std::endl;
  TNode mult = node[0];
  std::vector<Node> children;
  BitVector bv(utils::getSize(node), (unsigned)1);
  for(unsigned i = 0; i < mult.getNumChildren(); ++i) {
    if(mult[i].getKind() == kind::CONST_BITVECTOR) {
      bv = bv * mult[i].getConst<BitVector>();
    } else {
      children.push_back(mult[i]); 
    }
  }
  children.push_back(utils::mkConst(-bv));
  return utils::mkSortedNode(kind::BITVECTOR_MULT, children);
}

template<> inline
bool RewriteRule<NegSub>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_SUB);
}

template<> inline
Node RewriteRule<NegSub>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegSub>(" << node << ")" << std::endl;
  return utils::mkNode(kind::BITVECTOR_SUB, node[0][1], node[0][0]);
}

template<> inline
bool RewriteRule<NegPlus>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_PLUS);
}

template<> inline
Node RewriteRule<NegPlus>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<NegPlus>(" << node << ")" << std::endl;
  std::vector<Node> children;
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i) {
    children.push_back(utils::mkNode(kind::BITVECTOR_NEG, node[0][i])); 
  }
  return utils::mkSortedNode(kind::BITVECTOR_PLUS, children);
}




struct Count {
  unsigned pos;
  unsigned neg;
  Count() : pos(0), neg(0) {}
  Count(unsigned p, unsigned n):
    pos(p),
    neg(n)
  {}
};

inline static void insert(std::hash_map<TNode, Count, TNodeHashFunction>& map, TNode node, bool neg) {
  if(map.find(node) == map.end()) {
    Count c = neg? Count(0,1) : Count(1, 0);
    map[node] = c; 
  } else {
    if (neg) {
      ++(map[node].neg);
    } else {
      ++(map[node].pos);
    }
  }
}

template<> inline
bool RewriteRule<AndSimplify>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_AND);
}

template<> inline
Node RewriteRule<AndSimplify>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<AndSimplify>(" << node << ")" << std::endl;

  // this will remove duplicates
  std::hash_map<TNode, Count, TNodeHashFunction> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant = utils::mkBitVectorOnes(size); 
  
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector bv = current.getConst<BitVector>();
      constant = constant & bv;
    } else {
      if (current.getKind() == kind::BITVECTOR_NOT) {
        insert(subterms, current[0], true);
      } else {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;
  
  if (constant == BitVector(size, (unsigned)0)) {
    return utils::mkConst(BitVector(size, (unsigned)0)); 
  }

  if (constant != utils::mkBitVectorOnes(size)) {
    children.push_back(utils::mkConst(constant)); 
  }
  
  std::hash_map<TNode, Count, TNodeHashFunction>::const_iterator it = subterms.begin();

  for (; it != subterms.end(); ++it) {
    if (it->second.pos > 0 && it->second.neg > 0) {
      // if we have a and ~a 
      return utils::mkConst(BitVector(size, (unsigned)0)); 
    } else {
      // idempotence 
      if (it->second.neg > 0) {
        // if it only occured negated
        children.push_back(utils::mkNode(kind::BITVECTOR_NOT, it->first));
      } else {
        // if it only occured positive
        children.push_back(it->first); 
      }
    }
  }
  if (children.size() == 0) {
    return utils::mkOnes(size); 
  }
  
  return utils::mkSortedNode(kind::BITVECTOR_AND, children); 
}

template<> inline
bool RewriteRule<OrSimplify>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_OR);
}

template<> inline
Node RewriteRule<OrSimplify>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<OrSimplify>(" << node << ")" << std::endl;

  // this will remove duplicates
  std::hash_map<TNode, Count, TNodeHashFunction> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant(size, (unsigned)0); 
  
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector bv = current.getConst<BitVector>();
      constant = constant | bv;
    } else {
      if (current.getKind() == kind::BITVECTOR_NOT) {
        insert(subterms, current[0], true);
      } else {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;
  
  if (constant == utils::mkBitVectorOnes(size)) {
    return utils::mkOnes(size); 
  }

  if (constant != BitVector(size, (unsigned)0)) {
    children.push_back(utils::mkConst(constant)); 
  }
  
  std::hash_map<TNode, Count, TNodeHashFunction>::const_iterator it = subterms.begin();

  for (; it != subterms.end(); ++it) {
    if (it->second.pos > 0 && it->second.neg > 0) {
      // if we have a or ~a 
      return utils::mkOnes(size); 
    } else {
      // idempotence 
      if (it->second.neg > 0) {
        // if it only occured negated
        children.push_back(utils::mkNode(kind::BITVECTOR_NOT, it->first));
      } else {
        // if it only occured positive
        children.push_back(it->first); 
      }
    }
  }

  if (children.size() == 0) {
    return utils::mkConst(BitVector(size, (unsigned)0)); 
  }
  return utils::mkSortedNode(kind::BITVECTOR_OR, children); 
}

template<> inline
bool RewriteRule<XorSimplify>::applies(Node node) {
  return (node.getKind() == kind::BITVECTOR_XOR);
}

template<> inline
Node RewriteRule<XorSimplify>::apply(Node node) {
  BVDebug("bv-rewrite") << "RewriteRule<XorSimplify>(" << node << ")" << std::endl;


  std::hash_map<TNode, Count, TNodeHashFunction> subterms;
  unsigned size = utils::getSize(node);
  BitVector constant; 
  bool const_set = false; 

  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    // simplify constants
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector bv = current.getConst<BitVector>();
      if (const_set) {
        constant = constant ^ bv;
      } else {
        const_set = true; 
        constant = bv;
      }
    } else {
      // collect number of occurances of each term and its negation
      if (current.getKind() == kind::BITVECTOR_NOT) {
        insert(subterms, current[0], true);
      } else {
        insert(subterms, current, false);
      }
    }
  }

  std::vector<Node> children;

  std::hash_map<TNode, Count, TNodeHashFunction>::const_iterator it = subterms.begin();
  unsigned true_count = 0;
  bool seen_false = false; 
  for (; it != subterms.end(); ++it) {
    unsigned pos = it->second.pos; // number of positive occurances
    unsigned neg = it->second.neg; // number of negated occurances 

    // remove duplicates using the following rules
    // a xor a ==> false
    // false xor false ==> false
    seen_false = seen_false? seen_false : (pos > 1 || neg > 1);
    // check what did not reduce
    if (pos % 2 && neg % 2) {
      // we have a xor ~a ==> true
      ++true_count;
    } else if (pos % 2) {
      // we had a positive occurence left
      children.push_back(it->first); 
    } else if (neg % 2) {
      // we had a negative occurence left
      children.push_back(utils::mkNode(kind::BITVECTOR_NOT, it->first)); 
    }
    // otherwise both reduced to false
  }

  std::vector<BitVector> xorConst;
  BitVector true_bv = utils::mkBitVectorOnes(size);
  BitVector false_bv(size, (unsigned)0);
  
  if (true_count) {
    // true xor ... xor true ==> true (odd)
    //                       ==> false (even) 
    xorConst.push_back(true_count % 2? true_bv : false_bv); 
  }
  if (seen_false) {
    xorConst.push_back(false_bv); 
  }
  if(const_set) {
    xorConst.push_back(constant); 
  }

  if (xorConst.size() > 0) {
    BitVector result = xorConst[0];
    for (unsigned i = 1; i < xorConst.size(); ++i) {
      result = result ^ xorConst[i]; 
    }
    children.push_back(utils::mkConst(result)); 
  }

  Assert(children.size());
  
  return utils::mkSortedNode(kind::BITVECTOR_XOR, children); 
}




// template<> inline
// bool RewriteRule<AndSimplify>::applies(Node node) {
//   return (node.getKind() == kind::BITVECTOR_AND);
// }

// template<> inline
// Node RewriteRule<AndSimplify>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<AndSimplify>(" << node << ")" << std::endl;
//   return resultNode;
// }


// template<> inline
// bool RewriteRule<>::applies(Node node) {
//   return (node.getKind() == kind::BITVECTOR_CONCAT);
// }

// template<> inline
// Node RewriteRule<>::apply(Node node) {
//   BVDebug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return resultNode;
// }



}
}
}

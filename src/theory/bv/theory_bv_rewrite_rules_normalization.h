/*********************                                                        */
/*! \file theory_bv_rewrite_rules_normalization.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Clark Barrett, Tim King
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

#include "cvc4_private.h"

#pragma once

#include "theory/rewriter.h"
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
bool RewriteRule<ExtractBitwise>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_AND ||
           node[0].getKind() == kind::BITVECTOR_OR ||
           node[0].getKind() == kind::BITVECTOR_XOR ));
}

template<> inline
Node RewriteRule<ExtractBitwise>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractBitwise>(" << node << ")" << std::endl;
  unsigned high = utils::getExtractHigh(node);
  unsigned low = utils::getExtractLow(node);
  std::vector<Node> children; 
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i) {
    children.push_back(utils::mkExtract(node[0][i], high, low)); 
  }
  Kind kind = node[0].getKind(); 
  return utils::mkSortedNode(kind, children);
}

/**
 * ExtractNot
 *
 *  (~ a) [i:j] ==> ~ (a[i:j])
 */
template<> inline
bool RewriteRule<ExtractNot>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          node[0].getKind() == kind::BITVECTOR_NOT);
}

template<> inline
Node RewriteRule<ExtractNot>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractNot>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  Node a = utils::mkExtract(node[0][0], high, low);
  return utils::mkNode(kind::BITVECTOR_NOT, a); 
}

/** 
 * ExtractSignExtend
 * 
 * (sign_extend k x) [i:j] => pushes extract in
 * 
 * @return 
 */

template<> inline
bool RewriteRule<ExtractSignExtend>::applies(TNode node) {
  if (node.getKind() == kind::BITVECTOR_EXTRACT &&
      node[0].getKind() == kind::BITVECTOR_SIGN_EXTEND) {
    return true; 
  }
  return false; 
}

template<> inline
Node RewriteRule<ExtractSignExtend>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractSignExtend>(" << node << ")" << std::endl;
  TNode extendee = node[0][0]; 
  unsigned extendee_size = utils::getSize(extendee);

  unsigned high = utils::getExtractHigh(node);
  unsigned low = utils::getExtractLow(node); 

  Node resultNode; 
  // extract falls on extendee
  if (high < extendee_size) {
    resultNode = utils::mkExtract(extendee, high, low); 
  } else if (low < extendee_size && high >= extendee_size) {
    // if extract overlaps sign extend and extendee
    Node low_extract = utils::mkExtract(extendee, extendee_size - 1, low);
    unsigned new_ammount = high - extendee_size + 1;
    resultNode = utils::mkSignExtend(low_extract, new_ammount); 
  } else {
    // extract only over sign extend
    Assert (low >= extendee_size);
    unsigned top = utils::getSize(extendee) - 1; 
    Node most_significant_bit = utils::mkExtract(extendee, top, top);
    std::vector<Node> bits;
    for (unsigned i = 0; i < high - low + 1; ++i) {
      bits.push_back(most_significant_bit); 
    }
    resultNode =  utils::mkNode(kind::BITVECTOR_CONCAT, bits);
  }
  Debug("bv-rewrite") << "                           =>" << resultNode << std::endl;
  return resultNode; 
}



/**
 * ExtractArith
 * 
 * (a bvop b) [k:0] ==> (a[k:0] bvop b[k:0])
 */

template<> inline
bool RewriteRule<ExtractArith>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::getExtractLow(node) == 0 &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<> inline
Node RewriteRule<ExtractArith>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractArith>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  Assert (low == 0); 
  unsigned high = utils::getExtractHigh(node);
  std::vector<Node> children;
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i) {
    children.push_back(utils::mkExtract(node[0][i], high, low)); 
  }
  Kind kind = node[0].getKind(); 
  return utils::mkNode(kind, children); 
  
}

/**
 * ExtractArith2
 *
 * (a bvop b) [i:j] ==> (a[i:0] bvop b[i:0]) [i:j]
 */

// careful not to apply in a loop 
template<> inline
bool RewriteRule<ExtractArith2>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          (node[0].getKind() == kind::BITVECTOR_PLUS ||
           node[0].getKind() == kind::BITVECTOR_MULT));
}

template<> inline
Node RewriteRule<ExtractArith2>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ExtractArith2>(" << node << ")" << std::endl;
  unsigned low = utils::getExtractLow(node);
  unsigned high = utils::getExtractHigh(node);
  std::vector<Node> children;
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i) {
    children.push_back(utils::mkExtract(node[0][i], high, 0)); 
  }
  Kind kind = node[0].getKind(); 
  Node op_children = utils::mkNode(kind, children); 
  
  return utils::mkExtract(op_children, high, low); 
}

template<> inline
bool RewriteRule<FlattenAssocCommut>::applies(TNode node) {
  Kind kind = node.getKind();
  if (kind != kind::BITVECTOR_PLUS &&
      kind != kind::BITVECTOR_MULT &&
      kind != kind::BITVECTOR_OR &&
      kind != kind::BITVECTOR_XOR &&
      kind != kind::BITVECTOR_AND)
    return false;
  TNode::iterator child_it = node.begin();
  for(; child_it != node.end(); ++child_it) {
    if ((*child_it).getKind() == kind) {
      return true;
    }
  }
  return false;
}


template<> inline
Node RewriteRule<FlattenAssocCommut>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")" << std::endl;
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
  if (node.getKind() == kind::BITVECTOR_PLUS ||
      node.getKind() == kind::BITVECTOR_MULT) {
    return utils::mkNode(kind, children);
  }
  else {
    return utils::mkSortedNode(kind, children);
  }
}

static inline void addToCoefMap(std::map<Node, BitVector>& map,
                                TNode term, const BitVector& coef) {
  if (map.find(term) != map.end()) {
    map[term] = map[term] + coef; 
  } else {
    map[term] = coef;
  }
}


static inline void updateCoefMap(TNode current, unsigned size,
                                 std::map<Node, BitVector>& factorToCoefficient,
                                 BitVector& constSum) {
  switch (current.getKind()) {
    case kind::BITVECTOR_MULT: {
      // look for c * term, where c is a constant
      BitVector coeff;
      Node term;
      if (current.getNumChildren() == 2) {
        // Mult should be normalized with only one constant at end
        Assert(!current[0].isConst());
        if (current[1].isConst()) {
          coeff = current[1].getConst<BitVector>();
          term = current[0];
        }
      }
      else if (current[current.getNumChildren()-1].isConst()) {
        NodeBuilder<> nb(kind::BITVECTOR_MULT);
        TNode::iterator child_it = current.begin();
        for(; (child_it+1) != current.end(); ++child_it) {
          Assert(!(*child_it).isConst());
          nb << (*child_it);
        }
        term = nb;
        coeff = (*child_it).getConst<BitVector>();
      }
      if (term.isNull()) {
        coeff = BitVector(size, (unsigned)1);
        term = current;
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
      break;
    }
    case kind::BITVECTOR_SUB:
      // turn into a + (-1)*b 
      Assert(current.getNumChildren() == 2);
      addToCoefMap(factorToCoefficient, current[0], BitVector(size, (unsigned)1)); 
      addToCoefMap(factorToCoefficient, current[1], -BitVector(size, (unsigned)1)); 
      break;
    case kind::BITVECTOR_NEG:
      addToCoefMap(factorToCoefficient, current[0], -BitVector(size, (unsigned)1)); 
      break;
    case kind::CONST_BITVECTOR: {
      BitVector constValue = current.getConst<BitVector>(); 
      constSum = constSum + constValue;
      break;
    }
    default:
      // store as 1 * current
      addToCoefMap(factorToCoefficient, current, BitVector(size, (unsigned)1)); 
      break;
  }
}


static inline void addToChildren(TNode term, unsigned size, BitVector coeff, std::vector<Node>& children) {
  if (coeff == BitVector(size, (unsigned)0)) {
    return;
  }
  else if (coeff == BitVector(size, (unsigned)1)) {
    children.push_back(term); 
  }
  else if (coeff == -BitVector(size, (unsigned)1)) {
    // avoid introducing an extra multiplication
    children.push_back(utils::mkNode(kind::BITVECTOR_NEG, term)); 
  }
  else if (term.getKind() == kind::BITVECTOR_MULT) {
    NodeBuilder<> nb(kind::BITVECTOR_MULT);
    TNode::iterator child_it = term.begin();
    for(; child_it != term.end(); ++child_it) {
      nb << *child_it;
    }
    nb << utils::mkConst(coeff);
    children.push_back(Node(nb));
  }
  else {
    Node coeffNode = utils::mkConst(coeff);
    Node product = utils::mkNode(kind::BITVECTOR_MULT, term, coeffNode); 
    children.push_back(product); 
  }
}


template<> inline
bool RewriteRule<PlusCombineLikeTerms>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_PLUS);
}


template<> inline
Node RewriteRule<PlusCombineLikeTerms>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<PlusCombineLikeTerms>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constSum(size, (unsigned)0); 
  std::map<Node, BitVector> factorToCoefficient;

  // combine like-terms
  for(unsigned i= 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    updateCoefMap(current, size, factorToCoefficient, constSum);
  }
    
  std::vector<Node> children; 

  // construct result 
  std::map<Node, BitVector>::const_iterator it = factorToCoefficient.begin();
  
  for (; it != factorToCoefficient.end(); ++it) {
    addToChildren(it->first, size, it->second, children);
  }

  if (constSum != BitVector(size, (unsigned)0)) {
    children.push_back(utils::mkConst(constSum)); 
  }

  if(children.size() == 0) {
    return utils::mkConst(size, (unsigned)0); 
  }

  return utils::mkNode(kind::BITVECTOR_PLUS, children);
}


template<> inline
bool RewriteRule<MultSimplify>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT) {
    return false;
  }
  TNode::iterator child_it = node.begin();
  TNode::iterator child_next = child_it + 1;
  for(; child_next != node.end(); ++child_it, ++child_next) {
    if ((*child_it).isConst() ||
        !((*child_it) < (*child_next))) {
      return true;
    }
  }
  if ((*child_it).isConst()) {
    BitVector bv = (*child_it).getConst<BitVector>();
    if (bv == BitVector(utils::getSize(node), (unsigned) 0) ||
        bv == BitVector(utils::getSize(node), (unsigned) 1)) {
      return true;
    }
  }
  return false;
}

template<> inline
Node RewriteRule<MultSimplify>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<MultSimplify>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  BitVector constant(size, Integer(1));

  std::vector<Node> children; 
  for(unsigned i = 0; i < node.getNumChildren(); ++i) {
    TNode current = node[i];
    if (current.getKind() == kind::CONST_BITVECTOR) {
      BitVector value = current.getConst<BitVector>();
      constant = constant * value;
      if(constant == BitVector(size, (unsigned) 0)) {
        return utils::mkConst(size, 0); 
      }
    } else {
      children.push_back(current); 
    }
  }

  std::sort(children.begin(), children.end());

  if(constant != BitVector(size, (unsigned)1)) {
    children.push_back(utils::mkConst(constant)); 
  }
  
  if(children.size() == 0) {
    return utils::mkConst(size, (unsigned)1); 
  }

  return utils::mkNode(kind::BITVECTOR_MULT, children); 
}


template<> inline
bool RewriteRule<MultDistribConst>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT ||
      node.getNumChildren() != 2) {
    return false;
  }
  Assert(!node[0].isConst());
  if (!node[1].isConst()) {
    return false;
  }
  TNode factor = node[0];
  return (factor.getKind() == kind::BITVECTOR_PLUS ||
          factor.getKind() == kind::BITVECTOR_SUB ||
          factor.getKind() == kind::BITVECTOR_NEG); 
}

template<> inline
Node RewriteRule<MultDistribConst>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<MultDistribConst>(" << node << ")" << std::endl;

  TNode constant = node[1];
  TNode factor = node[0];
  Assert(constant.getKind() == kind::CONST_BITVECTOR);

  if (factor.getKind() == kind::BITVECTOR_NEG) {
    // push negation on the constant part
    BitVector const_bv = constant.getConst<BitVector>();
    return utils::mkNode(kind::BITVECTOR_MULT,
                         factor[0],
                         utils::mkConst(-const_bv)); 
  }

  std::vector<Node> children;
  for(unsigned i = 0; i < factor.getNumChildren(); ++i) {
    children.push_back(utils::mkNode(kind::BITVECTOR_MULT, factor[i], constant));
  }
  
  return utils::mkNode(factor.getKind(), children); 
}

template<> inline
bool RewriteRule<MultDistrib>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_MULT ||
      node.getNumChildren() != 2) {
    return false;
  }
  if (node[0].getKind() == kind::BITVECTOR_PLUS ||
      node[0].getKind() == kind::BITVECTOR_SUB) {
    return node[1].getKind() != kind::BITVECTOR_PLUS &&
           node[1].getKind() != kind::BITVECTOR_SUB;
  }
  return node[1].getKind() == kind::BITVECTOR_PLUS ||
         node[1].getKind() == kind::BITVECTOR_SUB; 
}

template<> inline
Node RewriteRule<MultDistrib>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<MultDistrib>(" << node << ")" << std::endl;

  bool is_rhs_factor = node[0].getKind() == kind::BITVECTOR_PLUS ||
                       node[0].getKind() == kind::BITVECTOR_SUB;
  TNode factor = !is_rhs_factor ? node[0] : node[1];
  TNode sum = is_rhs_factor ? node[0] : node[1];
  Assert (factor.getKind() != kind::BITVECTOR_PLUS &&
          factor.getKind() != kind::BITVECTOR_SUB &&
          (sum.getKind() == kind::BITVECTOR_PLUS ||
           sum.getKind() == kind::BITVECTOR_SUB));

  std::vector<Node> children;
  for(unsigned i = 0; i < sum.getNumChildren(); ++i) {
    children.push_back(utils::mkNode(kind::BITVECTOR_MULT, sum[i], factor));
  }
  
  return utils::mkNode(sum.getKind(), children); 
}

template<> inline
bool RewriteRule<ConcatToMult>::applies(TNode node) {
  if (node.getKind() != kind::BITVECTOR_CONCAT) return false;
  if (node.getNumChildren() != 2) return false;
  if (node[0].getKind()!= kind::BITVECTOR_EXTRACT) return false;
  if (!node[1].isConst()) return false;
  TNode extract = node[0];
  TNode c = node[1];
  unsigned ammount = utils::getSize(c);
  
  if (utils::getSize(node) != utils::getSize(extract[0])) return false; 
  if (c != utils::mkConst(ammount, 0)) return false;

  unsigned low = utils::getExtractLow(extract);
  if (low != 0) return false; 
  unsigned high = utils::getExtractHigh(extract);
  if (high + ammount + 1 != utils::getSize(node)) return false;
  return true;
}

template<> inline
Node RewriteRule<ConcatToMult>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<ConcatToMult>(" << node << ")" << std::endl;
  unsigned size = utils::getSize(node); 
  Node factor = node[0][0];
  Assert(utils::getSize(factor) == utils::getSize(node)); 
  BitVector ammount = BitVector(size, utils::getSize(node[1]));
  Node coef = utils::mkConst(BitVector(size, 1u).leftShift(ammount));
  return utils::mkNode(kind::BITVECTOR_MULT, factor, coef); 
}



template<> inline
bool RewriteRule<SolveEq>::applies(TNode node) {
  if (node.getKind() != kind::EQUAL ||
      (node[0].isVar() && !node[1].hasSubterm(node[0])) ||
      (node[1].isVar() && !node[0].hasSubterm(node[1]))) {
    return false;
  }
  return true;
}


// Doesn't do full solving (yet), instead, if a term appears both on lhs and rhs, it subtracts from both sides so that one side's coeff is zero
template<> inline
Node RewriteRule<SolveEq>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<SolveEq>(" << node << ")" << std::endl;

  TNode left = node[0];
  TNode right = node[1];

  unsigned size = utils::getSize(left);
  BitVector zero(size, (unsigned)0);
  BitVector leftConst(size, (unsigned)0);
  BitVector rightConst(size, (unsigned)0);
  std::map<Node, BitVector> leftMap, rightMap;

  // Collect terms and coefficients plus constant for left
  if (left.getKind() == kind::BITVECTOR_PLUS) {
    for(unsigned i= 0; i < left.getNumChildren(); ++i) {
      updateCoefMap(left[i], size, leftMap, leftConst);
    }
  }
  else if (left.getKind() == kind::BITVECTOR_NOT && left[0] == right) {
    return utils::mkFalse();
  }
  else {
    updateCoefMap(left, size, leftMap, leftConst);
  }

  // Collect terms and coefficients plus constant for right
  if (right.getKind() == kind::BITVECTOR_PLUS) {
    for(unsigned i= 0; i < right.getNumChildren(); ++i) {
      updateCoefMap(right[i], size, rightMap, rightConst);
    }
  }
  else if (right.getKind() == kind::BITVECTOR_NOT && right[0] == left) {
    return utils::mkFalse();
  }
  else {
    updateCoefMap(right, size, rightMap, rightConst);
  }

  std::vector<Node> childrenLeft, childrenRight;

  std::map<Node, BitVector>::const_iterator iLeft = leftMap.begin(), iLeftEnd = leftMap.end();
  std::map<Node, BitVector>::const_iterator iRight = rightMap.begin(), iRightEnd = rightMap.end();

  BitVector coeffLeft;
  TNode termLeft;
  if (iLeft != iLeftEnd) {
    coeffLeft = iLeft->second;
    termLeft = iLeft->first;
  }

  BitVector coeffRight;
  TNode termRight;
  if (iRight != iRightEnd) {
    coeffRight = iRight->second;
    termRight = iRight->first;
  }

  bool incLeft, incRight;

  while (iLeft != iLeftEnd || iRight != iRightEnd) {
    incLeft = incRight = false;
    if (iLeft != iLeftEnd && (iRight == iRightEnd || termLeft < termRight)) {
      addToChildren(termLeft, size, coeffLeft, childrenLeft);
      incLeft = true;
    }      
    else if (iLeft == iLeftEnd || termRight < termLeft) {
      Assert(iRight != iRightEnd);
      addToChildren(termRight, size, coeffRight, childrenRight);
      incRight = true;
    }
    else {
      if (coeffLeft > coeffRight) {
        addToChildren(termLeft, size, coeffLeft - coeffRight, childrenLeft);
      }
      else if (coeffRight > coeffLeft) {
        addToChildren(termRight, size, coeffRight - coeffLeft, childrenRight);
      }
      incLeft = incRight = true;
    }
    if (incLeft) {
      ++iLeft;
      if (iLeft != iLeftEnd) {
        Assert(termLeft < iLeft->first);
        coeffLeft = iLeft->second;
        termLeft = iLeft->first;
      }
    }
    if (incRight) {
      ++iRight;
      if (iRight != iRightEnd) {
        Assert(termRight < iRight->first);
        coeffRight = iRight->second;
        termRight = iRight->first;
      }
    }
  }

  // construct result 

  // If both constants are nonzero, combine on right, otherwise leave them where they are
  if (rightConst != zero) {
    rightConst = rightConst - leftConst;
    leftConst = zero;
    if (rightConst != zero) {
      childrenRight.push_back(utils::mkConst(rightConst));
    }
  }
  else if (leftConst != zero) {
    childrenLeft.push_back(utils::mkConst(leftConst));
  }

  Node newLeft, newRight;

  if(childrenRight.size() == 0 && leftConst != zero) {
    Assert(childrenLeft.back().isConst() && childrenLeft.back().getConst<BitVector>() == leftConst);
    if (childrenLeft.size() == 1) {
      // c = 0 ==> false
      return utils::mkFalse();
    }
    // special case - if right is empty and left has a constant, move the constant
    childrenRight.push_back(utils::mkConst(-leftConst));
    childrenLeft.pop_back();
  }

  if(childrenLeft.size() == 0) {
    if (rightConst != zero) {
      Assert(childrenRight.back().isConst() && childrenRight.back().getConst<BitVector>() == rightConst);
      if (childrenRight.size() == 1) {
        // 0 = c ==> false
        return utils::mkFalse();
      }
      // special case - if left is empty and right has a constant, move the constant
      newLeft = utils::mkConst(-rightConst);
      childrenRight.pop_back();
    }
    else {
      newLeft = utils::mkConst(size, (unsigned)0); 
    }
  }
  else if (childrenLeft.size() == 1) {
    newLeft = childrenLeft[0];
  }
  else {
    newLeft = utils::mkNode(kind::BITVECTOR_PLUS, childrenLeft);
  }

  if (childrenRight.size() == 0) {
    newRight = utils::mkConst(size, (unsigned)0);
  }
  else if (childrenRight.size() == 1) {
    newRight = childrenRight[0];
  }
  else {
    newRight = utils::mkNode(kind::BITVECTOR_PLUS, childrenRight);
  }

  //  Assert(newLeft == Rewriter::rewrite(newLeft));
  //  Assert(newRight == Rewriter::rewrite(newRight));

  if (newLeft == newRight) {
    Assert (newLeft == utils::mkConst(size, (unsigned)0));
    return utils::mkTrue();
  }

  if (newLeft < newRight) {
    Assert((newRight == left && newLeft == right) ||
           Rewriter::rewrite(newRight) != left ||
           Rewriter::rewrite(newLeft) != right);
    return newRight.eqNode(newLeft);
  }
  
  Assert((newLeft == left && newRight == right) ||
         Rewriter::rewrite(newLeft) != left ||
         Rewriter::rewrite(newRight) != right);
  return newLeft.eqNode(newRight);
}


template<> inline
bool RewriteRule<BitwiseEq>::applies(TNode node) {
  if (node.getKind() != kind::EQUAL ||
      utils::getSize(node[0]) != 1) {
    return false;
  }
  TNode term;
  BitVector c;
  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    c = node[0].getConst<BitVector>();
    term = node[1];
  }
  else if (node[1].getKind() == kind::CONST_BITVECTOR) {
    c = node[1].getConst<BitVector>();
    term = node[0];
  }
  else {
    return false;
  }
  switch (term.getKind()) {
    case kind::BITVECTOR_AND:
    case kind::BITVECTOR_OR:
      //operator BITVECTOR_XOR 2: "bitwise xor"
    case kind::BITVECTOR_NOT:
    case kind::BITVECTOR_NAND:
    case kind::BITVECTOR_NOR:
      //operator BITVECTOR_XNOR 2 "bitwise xnor"
    case kind::BITVECTOR_COMP:
    case kind::BITVECTOR_NEG:
      return true;
      break;
    default:
      break;
  }
  return false;
}


static inline Node mkNodeKind(Kind k, TNode node, TNode c) {
  unsigned i = 0;
  unsigned nc = node.getNumChildren();
  NodeBuilder<> nb(k);
  for(; i < nc; ++i) {
    nb << node[i].eqNode(c);
  }
  return nb;
}


template<> inline
Node RewriteRule<BitwiseEq>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<BitwiseEq>(" << node << ")" << std::endl;

  TNode term;
  BitVector c;

  if (node[0].getKind() == kind::CONST_BITVECTOR) {
    c = node[0].getConst<BitVector>();
    term = node[1];
  }
  else if (node[1].getKind() == kind::CONST_BITVECTOR) {
    c = node[1].getConst<BitVector>();
    term = node[0];
  }

  bool eqOne = (c == BitVector(1,(unsigned)1));

  switch (term.getKind()) {
    case kind::BITVECTOR_AND:
      if (eqOne) {
        return mkNodeKind(kind::AND, term, utils::mkConst(1, (unsigned)1));
      }
      else {
        return mkNodeKind(kind::OR, term, utils::mkConst(1, (unsigned)0));
      }
      break;
    case kind::BITVECTOR_NAND:
      if (eqOne) {
        return mkNodeKind(kind::OR, term, utils::mkConst(1, (unsigned)0));
      }
      else {
        return mkNodeKind(kind::AND, term, utils::mkConst(1, (unsigned)1));
      }
      break;
    case kind::BITVECTOR_OR:
      if (eqOne) {
        return mkNodeKind(kind::OR, term, utils::mkConst(1, (unsigned)1));
      }
      else {
        return mkNodeKind(kind::AND, term, utils::mkConst(1, (unsigned)0));
      }
      break;
    case kind::BITVECTOR_NOR:
      if (eqOne) {
        return mkNodeKind(kind::AND, term, utils::mkConst(1, (unsigned)0));
      }
      else {
        return mkNodeKind(kind::OR, term, utils::mkConst(1, (unsigned)1));
      }
      break;
    case kind::BITVECTOR_NOT:
      return term[0].eqNode(utils::mkConst(~c));
    case kind::BITVECTOR_COMP:
      Assert(term.getNumChildren() == 2);
      if (eqOne) {
        return term[0].eqNode(term[1]);
      }
      else {
        return term[0].eqNode(term[1]).notNode();
      }
    case kind::BITVECTOR_NEG:
      return term[0].eqNode(utils::mkConst(c));
    default:
      break;
  }
  Unreachable();
}


/**
 * -(c * expr) ==> (-c * expr)
 * where c is a constant
 */
template<> inline
bool RewriteRule<NegMult>::applies(TNode node) {
  if(node.getKind()!= kind::BITVECTOR_NEG ||
     node[0].getKind() != kind::BITVECTOR_MULT) {                                
    return false;
  }
  return node[node.getNumChildren()-1].isConst();
}

template<> inline
Node RewriteRule<NegMult>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NegMult>(" << node << ")" << std::endl;
  TNode mult = node[0];
  NodeBuilder<> nb(kind::BITVECTOR_MULT);
  BitVector bv(utils::getSize(node), (unsigned)1);
  TNode::iterator child_it = mult.begin();
  for(; (child_it+1) != mult.end(); ++child_it) {
    nb << (*child_it);
  }
  Assert((*child_it).isConst());
  bv = (*child_it).getConst<BitVector>();
  nb << utils::mkConst(-bv);
  return Node(nb);
}

template<> inline
bool RewriteRule<NegSub>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_SUB);
}

template<> inline
Node RewriteRule<NegSub>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NegSub>(" << node << ")" << std::endl;
  return utils::mkNode(kind::BITVECTOR_SUB, node[0][1], node[0][0]);
}

template<> inline
bool RewriteRule<NegPlus>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          node[0].getKind() == kind::BITVECTOR_PLUS);
}

template<> inline
Node RewriteRule<NegPlus>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<NegPlus>(" << node << ")" << std::endl;
  std::vector<Node> children;
  for (unsigned i = 0; i < node[0].getNumChildren(); ++i) {
    children.push_back(utils::mkNode(kind::BITVECTOR_NEG, node[0][i])); 
  }
  return utils::mkNode(kind::BITVECTOR_PLUS, children);
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
bool RewriteRule<AndSimplify>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_AND);
}

template<> inline
Node RewriteRule<AndSimplify>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<AndSimplify>(" << node << ")" << std::endl;

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
bool RewriteRule<FlattenAssocCommutNoDuplicates>::applies(TNode node) {
  Kind kind = node.getKind();
  if (kind != kind::BITVECTOR_OR &&
      kind != kind::BITVECTOR_AND)
    return false;
  TNode::iterator child_it = node.begin();
  for(; child_it != node.end(); ++child_it) {
    if ((*child_it).getKind() == kind) {
      return true;
    }
  }
  return false;
}
  
template<> inline
Node RewriteRule<FlattenAssocCommutNoDuplicates>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<FlattenAssocCommut>(" << node << ")" << std::endl;
  std::vector<Node> processingStack;
  processingStack.push_back(node);
  __gnu_cxx::hash_set<TNode, TNodeHashFunction> processed;
  std::vector<Node> children;
  Kind kind = node.getKind(); 
  
  while (! processingStack.empty()) {
    TNode current = processingStack.back();
    processingStack.pop_back();
    if (processed.count(current))
      continue;

    processed.insert(current);
    
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
  
  
template<> inline
bool RewriteRule<OrSimplify>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_OR);
}

template<> inline
Node RewriteRule<OrSimplify>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<OrSimplify>(" << node << ")" << std::endl;

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
bool RewriteRule<XorSimplify>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_XOR);
}

template<> inline
Node RewriteRule<XorSimplify>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<XorSimplify>(" << node << ")" << std::endl;


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


/** 
 * BitwiseSlicing
 * 
 * (a bvand c) ==> (concat (bvand a[i0:j0] c0) ... (bvand a[in:jn] cn))
 *  where c0,..., cn are maximally continuous substrings of 0 or 1 in the constant c 
 *
 * Note: this rule assumes AndSimplify has already been called on the node
 */
template<> inline
bool RewriteRule<BitwiseSlicing>::applies(TNode node) {
  if ((node.getKind() != kind::BITVECTOR_AND &&
      node.getKind() != kind::BITVECTOR_OR &&
      node.getKind() != kind::BITVECTOR_XOR) ||
      utils::getSize(node) == 1)
    return false; 
  // find the first constant and return true if it's not only 1..1 or only 0..0
  // (there could be more than one constant)
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind() == kind::CONST_BITVECTOR) {
      BitVector constant = node[i].getConst<BitVector>();
      // we do not apply the rule if the constant is all 0s or all 1s
      if (constant == BitVector(utils::getSize(node), 0u)) 
        return false; 
      
      for (unsigned i = 0; i < constant.getSize(); ++i) {
        if (!constant.isBitSet(i)) 
          return true; 
      }
      return false; 
    }
  }
  return false; 
}

template<> inline
Node RewriteRule<BitwiseSlicing>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<BitwiseSlicing>(" << node << ")" << std::endl;
  // get the constant
  bool found_constant = false ;
  TNode constant;
  std::vector<Node> other_children; 
  for (unsigned i = 0; i < node.getNumChildren(); ++i) {
    if (node[i].getKind() == kind::CONST_BITVECTOR && !found_constant) {
      constant = node[i];
      found_constant = true; 
    } else {
      other_children.push_back(node[i]); 
    }
  }
  Assert (found_constant && other_children.size() == node.getNumChildren() - 1);

  Node other = utils::mkNode(node.getKind(), other_children);
  
  BitVector bv_constant = constant.getConst<BitVector>();
  std::vector<Node> concat_children; 
  int start = bv_constant.getSize() - 1;
  int end = start;
  for (int i = end - 1; i >= 0; --i) {
    if (bv_constant.isBitSet(i + 1) != bv_constant.isBitSet(i)) {
      Node other_extract = utils::mkExtract(other, end, start);
      Node const_extract = utils::mkExtract(constant, end, start);
      Node bitwise_op = utils::mkNode(node.getKind(), const_extract, other_extract);
      concat_children.push_back(bitwise_op);
      start = end = i; 
    } else {
      start--; 
    }
    if (i == 0) {
      Node other_extract = utils::mkExtract(other, end, 0);
      Node const_extract = utils::mkExtract(constant, end, 0);
      Node bitwise_op = utils::mkNode(node.getKind(), const_extract, other_extract);
      concat_children.push_back(bitwise_op);
    }

  }
  Node result = utils::mkNode(kind::BITVECTOR_CONCAT, concat_children);
  Debug("bv-rewrite") << "    =>" << result << std::endl;
  return result;
}

// template<> inline
// bool RewriteRule<>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_CONCAT);
// }

// template<> inline
// Node RewriteRule<>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<>(" << node << ")" << std::endl;
//   return resultNode;
// }



}
}
}

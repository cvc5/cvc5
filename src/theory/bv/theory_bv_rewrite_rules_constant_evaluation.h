/*********************                                                        */
/*! \file theory_bv_rewrite_rules_constant_evaluation.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Clark Barrett, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/bv/theory_bv_utils.h"

namespace CVC4 {
namespace theory {
namespace bv {

template<> inline
bool RewriteRule<EvalAnd>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_AND &&
          node.getNumChildren() == 2 &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalAnd>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<EvalAnd>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a & b;
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalOr>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_OR &&
          node.getNumChildren() == 2 &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalOr>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<EvalOr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a | b;
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalXor>::applies(TNode node) {
  Unreachable();
  return (node.getKind() == kind::BITVECTOR_XOR &&
          node.getNumChildren() == 2 &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalXor>::apply(TNode node) {
  Unreachable();
  Debug("bv-rewrite") << "RewriteRule<EvalXor>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a ^ b;
 
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalXnor>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_XNOR &&
//           utils::isBvConstTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalXnor>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<EvalXnor>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res = ~ (a ^ b);
  
//   return utils::mkConst(res);
// }
template<> inline
bool RewriteRule<EvalNot>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NOT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalNot>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalNot>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = ~ a;
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalComp>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_COMP &&
//           utils::isBvConstTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalComp>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<EvalComp>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res;
//   if (a == b) {
//     res = BitVector(1, Integer(1));
//   } else {
//     res = BitVector(1, Integer(0)); 
//   }
  
//   return utils::mkConst(res);
// }

template<> inline
bool RewriteRule<EvalMult>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_MULT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalMult>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalMult>(" << node << ")" << std::endl;
  TNode::iterator child_it = node.begin();
  BitVector res = (*child_it).getConst<BitVector>();
  for(++child_it; child_it != node.end(); ++child_it) {
    res = res * (*child_it).getConst<BitVector>();
  }
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalPlus>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_PLUS &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalPlus>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalPlus>(" << node << ")" << std::endl;
  TNode::iterator child_it = node.begin();
  BitVector res = (*child_it).getConst<BitVector>();
  for(++child_it; child_it != node.end(); ++child_it) {
    res = res + (*child_it).getConst<BitVector>();
  }
  return utils::mkConst(res);
}

// template<> inline
// bool RewriteRule<EvalSub>::applies(TNode node) {
//   return (node.getKind() == kind::BITVECTOR_SUB &&
//           utils::isBvConstTerm(node));
// }

// template<> inline
// Node RewriteRule<EvalSub>::apply(TNode node) {
//   Debug("bv-rewrite") << "RewriteRule<EvalSub>(" << node << ")" << std::endl;
//   BitVector a = node[0].getConst<BitVector>();
//   BitVector b = node[1].getConst<BitVector>();
//   BitVector res = a - b;
  
//   return utils::mkConst(res);
// }
template<> inline
bool RewriteRule<EvalNeg>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_NEG &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalNeg>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalNeg>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector res = - a;
  
  return utils::mkConst(res);
}
template<> inline
bool RewriteRule<EvalUdiv>::applies(TNode node) {
  return (utils::isBvConstTerm(node) &&
          (node.getKind() == kind::BITVECTOR_UDIV_TOTAL ||
           (node.getKind() == kind::BITVECTOR_UDIV && node[1].isConst())));
}

template<> inline
Node RewriteRule<EvalUdiv>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalUdiv>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedDivTotal(b);
  
  return utils::mkConst(res);
}
template<> inline
bool RewriteRule<EvalUrem>::applies(TNode node) {
  return (utils::isBvConstTerm(node) &&
          (node.getKind() == kind::BITVECTOR_UREM_TOTAL ||
           (node.getKind() == kind::BITVECTOR_UREM && node[1].isConst())));
}

template<> inline
Node RewriteRule<EvalUrem>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalUrem>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  BitVector res = a.unsignedRemTotal(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalShl>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SHL &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalShl>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalShl>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.leftShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalLshr>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_LSHR &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalLshr>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalLshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  
  BitVector res = a.logicalRightShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalAshr>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ASHR &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalAshr>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalAshr>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  BitVector res = a.arithRightShift(b);
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalUlt>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalUlt>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalUlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.unsignedLessThan(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalUltBv>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULTBV &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalUltBv>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalUltBv>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.unsignedLessThan(b)) {
    return utils::mkConst(1,1);
  }
  return utils::mkConst(1, 0);
}

template<> inline
bool RewriteRule<EvalSlt>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalSlt>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalSlt>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.signedLessThan(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();

}

template<> inline
bool RewriteRule<EvalSltBv>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLTBV &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalSltBv>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalSltBv>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.signedLessThan(b)) {
    return utils::mkConst(1, 1);
  }
  return utils::mkConst(1, 0);

}

template<> inline
bool RewriteRule<EvalITEBv>::applies(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalITEBv>::applies(" << node << ")" << std::endl;
  return (node.getKind() == kind::BITVECTOR_ITE &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalITEBv>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalITEBv>(" << node << ")" << std::endl;
  BitVector cond = node[0].getConst<BitVector>();

  if (node[0] == utils::mkConst(1, 1)) {
    return node[1];
  } else {
    Assert(node[0] == utils::mkConst(1, 0));
    return node[2];
  }
}

template<> inline
bool RewriteRule<EvalUle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_ULE &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalUle>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalUle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.unsignedLessThanEq(b)) {
    return utils::mkTrue();
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalSle>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SLE &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalSle>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalSle>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();

  if (a.signedLessThanEq(b)) {
    return utils::mkTrue(); 
  }
  return utils::mkFalse();
}

template<> inline
bool RewriteRule<EvalExtract>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_EXTRACT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalExtract>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalExtract>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned lo = utils::getExtractLow(node);
  unsigned hi = utils::getExtractHigh(node);

  BitVector res = a.extract(hi, lo);
  return utils::mkConst(res);
}


template<> inline
bool RewriteRule<EvalConcat>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_CONCAT &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalConcat>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalConcat>(" << node << ")" << std::endl;
  unsigned num = node.getNumChildren();
  BitVector res = node[0].getConst<BitVector>();
  for(unsigned i = 1; i < num; ++i ) {  
    BitVector a = node[i].getConst<BitVector>();
    res = res.concat(a); 
  }
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalSignExtend>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_SIGN_EXTEND &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalSignExtend>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalSignExtend>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  unsigned amount =
      node.getOperator().getConst<BitVectorSignExtend>().d_signExtendAmount;
  BitVector res = a.signExtend(amount);
  
  return utils::mkConst(res);
}

template<> inline
bool RewriteRule<EvalEquals>::applies(TNode node) {
  return (node.getKind() == kind::EQUAL &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalEquals>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalEquals>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  if (a == b) {
    return utils::mkTrue(); 
  }
  return utils::mkFalse();

}

template<> inline
bool RewriteRule<EvalComp>::applies(TNode node) {
  return (node.getKind() == kind::BITVECTOR_COMP &&
          utils::isBvConstTerm(node));
}

template<> inline
Node RewriteRule<EvalComp>::apply(TNode node) {
  Debug("bv-rewrite") << "RewriteRule<EvalComp>(" << node << ")" << std::endl;
  BitVector a = node[0].getConst<BitVector>();
  BitVector b = node[1].getConst<BitVector>();
  if (a == b) {
    return utils::mkConst(1, 1);
  }
  return utils::mkConst(1, 0);
}

}
}
}

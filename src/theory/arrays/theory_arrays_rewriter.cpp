/*********************                                                        */
/*! \file theory_arrays_rewriter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
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

#include "expr/attribute.h"
#include "theory/arrays/theory_arrays_rewriter.h"
#include "proof/rewrite_proof_dispatcher.h"

namespace CVC4 {
namespace theory {
namespace arrays {

void TheoryArraysRewriter::printRewriteProof(TheoryProofEngine* tp,
                                             const Rewrite& rewrite,
                                             std::ostream& os,
                                             ProofLetMap& globalLetMap) {
  if (rewrite.d_tag == ORIGINAL_OP && rewrite.d_children.size() == 0) {
    switch (rewrite.d_original.getKind()) {
      case kind::EQUAL:
        os << "(iff_symm ";
        tp->printTheoryTerm(rewrite.d_original.toExpr(), os, globalLetMap);
        os << ")";
        break;
      default:
        os << "(refl _ ";
        tp->printTheoryTerm(rewrite.d_original.toExpr(), os, globalLetMap);
        os << ")";
        break;
    }
  } else if (rewrite.d_tag == EQ) {
    os << "(iff_true _ _ _ ";
    callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
    os << ")";
  } else if (rewrite.d_tag == ORIGINAL_OP) {
    switch (rewrite.d_original.getKind()) {
      case kind::EQUAL:
        os << "(iff_intro _ _ _ _ _ ";
        callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
        os << " ";
        callPrintRewriteProof(tp, rewrite.d_children[1], os, globalLetMap);
        os << ")";
        break;
      case kind::SELECT:
        os << "(cong _ _ _ _ _ _ (cong _ _ _ _ _ _ ";
        os << "(refl _ (read ";
        tp->printSort(ArrayType(rewrite.d_original.toExpr()[0].getType()).getIndexType(), os);
        os << " ";
        tp->printSort(ArrayType(rewrite.d_original.toExpr()[0].getType()).getConstituentType(), os);
        os << ")) ";
        callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
        os << ") ";
        callPrintRewriteProof(tp, rewrite.d_children[1], os, globalLetMap);
        os << ")";
        break;
      default:
        std::cout << "ERROR!" << rewrite.d_original.getKind() << std::endl;
        callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
        Unreachable();
    }
  } else if (rewrite.d_tag == WOR) {
    os << "(wor _ _ _ _ _ ";
    callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
    os << ")";
  } else if (rewrite.d_tag == WOW) {
    os << "(wow _ _ _ _ _ _ _ _ _ _ ";
    callPrintRewriteProof(tp, rewrite.d_children[0], os, globalLetMap);
    os << " ";
    callPrintRewriteProof(tp, rewrite.d_children[1], os, globalLetMap);
    os << " ";
    callPrintRewriteProof(tp, rewrite.d_children[2], os, globalLetMap);
    os << " ";
    callPrintRewriteProof(tp, rewrite.d_children[3], os, globalLetMap);
    os << ")";
  } else {
    std::cout << "ERROR" << rewrite.d_tag << std::endl;
    Unreachable();
  }
}

namespace attr {
  struct ArrayConstantMostFrequentValueTag { };
  struct ArrayConstantMostFrequentValueCountTag { };
}/* CVC4::theory::arrays::attr namespace */

typedef expr::Attribute<attr::ArrayConstantMostFrequentValueCountTag, uint64_t> ArrayConstantMostFrequentValueCountAttr;
typedef expr::Attribute<attr::ArrayConstantMostFrequentValueTag, Node> ArrayConstantMostFrequentValueAttr;

Node getMostFrequentValue(TNode store) {
  return store.getAttribute(ArrayConstantMostFrequentValueAttr());
}
uint64_t getMostFrequentValueCount(TNode store) {
  return store.getAttribute(ArrayConstantMostFrequentValueCountAttr());
}

void setMostFrequentValue(TNode store, TNode value) {
  return store.setAttribute(ArrayConstantMostFrequentValueAttr(), value);
}
void setMostFrequentValueCount(TNode store, uint64_t count) {
  return store.setAttribute(ArrayConstantMostFrequentValueCountAttr(), count);
}

}/* CVC4::theory::arrays namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

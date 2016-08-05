// TODO: decide whether this should be part of rewriter_tables
#include "proof/rewrite_proof_dispatcher.h"

#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/booleans/theory_bool_rewriter.h"

namespace CVC4 {

void printProof(TheoryProofEngine *tp, const RewriteProof &rp, std::ostream &os,
                ProofLetMap &globalLetMap) {
  //Assert(d_rewrites.size() == 1);
  //std::cout << std::endl;
  //rp.getRewrite().print(0);
  callPrintRewriteProof(tp, rp.getRewrite(), os, globalLetMap);
}

theory::RewriteResponse callPreRewriteWithProof(TNode node, const Rewrite& currentRewrite) {
  switch (theory::theoryOf(currentRewrite.d_original)) {
    case theory::THEORY_ARRAY:
      return theory::arrays::TheoryArraysRewriter::preRewriteEx<true>(node);

    case theory::THEORY_BOOL:
      return theory::booleans::TheoryBoolRewriter::preRewrite(node);

    default:
      Unreachable();
  }
}

theory::RewriteResponse callPostRewriteWithProof(TNode node, const Rewrite& currentRewrite) {
  switch (theory::theoryOf(currentRewrite.d_original)) {
    case theory::THEORY_ARRAY:
      return theory::arrays::TheoryArraysRewriter::postRewriteEx<true>(node, &currentRewrite);

    case theory::THEORY_BOOL:
      return theory::booleans::TheoryBoolRewriter::postRewrite(node);

    default:
      Unreachable();
  }
}

void callPrintRewriteProof(TheoryProofEngine *tp, const Rewrite &rewrite,
                       std::ostream &os, ProofLetMap &globalLetMap) {
  switch (theory::theoryOf(rewrite.d_original)) {
    case theory::THEORY_ARRAY:
      theory::arrays::TheoryArraysRewriter::printRewriteProof(tp, rewrite,
                                                              os, globalLetMap);
      break;

    case theory::THEORY_BOOL:
      theory::booleans::TheoryBoolRewriter::printRewriteProof(tp, rewrite,
                                                              os, globalLetMap);
      break;

    default:
      for (size_t i = 0; i < rewrite.d_children.size(); i++) {
        callPrintRewriteProof(tp, rewrite.d_children[i], os, globalLetMap);
        std::cout << std::endl;
      }
      break;
  }
}

} /* CVC4 namespace */

// TODO: decide whether this should be part of rewriter_tables
#include "proof/rewrite_proof_dispatcher.h"

#include "theory/arrays/theory_arrays_rewriter.h"
#include "theory/booleans/theory_bool_rewriter.h"

namespace CVC4 {

void printProof(TheoryProofEngine *tp, const RewriteProof &rp, std::ostream &os,
                ProofLetMap &globalLetMap) {
  std::ostringstream paren;
  rp.printCachedProofs(tp, os, paren, globalLetMap);
  os << std::endl;
  callPrintRewriteProof(true, tp, rp.getRewrite(), os, globalLetMap);
  os << paren.str();
}

theory::RewriteResponse callPreRewriteWithProof(theory::TheoryId theory,
                                                TNode node,
                                                RewriteProof *proof) {
  Assert(proof);
  switch (theory) {
  case theory::THEORY_ARRAY:
    return theory::arrays::TheoryArraysRewriter::preRewriteEx<true>(node,
                                                                    proof);

  case theory::THEORY_BOOL:
    return theory::booleans::TheoryBoolRewriter::preRewriteEx<true>(node,
                                                                    proof);

  default:
    Unreachable();
  }
}

theory::RewriteResponse callPostRewriteWithProof(theory::TheoryId theory,
                                                 TNode node,
                                                 RewriteProof *proof) {
  Assert(proof);
  switch (theory) {
  case theory::THEORY_ARRAY:
    return theory::arrays::TheoryArraysRewriter::postRewriteEx<true>(node,
                                                                     proof);

  case theory::THEORY_BOOL:
    return theory::booleans::TheoryBoolRewriter::postRewriteEx<true>(node,
                                                                     proof);

  default:
    Unreachable();
  }
}

void callPrintRewriteProof(bool use_cache, TheoryProofEngine *tp,
                           const Rewrite *rewrite, std::ostream &os,
                           ProofLetMap &globalLetMap) {
  if (use_cache && rewrite->d_cached_version_used) {
    os << "let" << rewrite->d_id;
    return;
  }

  switch (theory::theoryOf(rewrite->d_original)) {
  case theory::THEORY_ARRAY:
    theory::arrays::TheoryArraysRewriter::printRewriteProof(
        use_cache, tp, rewrite, os, globalLetMap);
    break;

  case theory::THEORY_BOOL:
    theory::booleans::TheoryBoolRewriter::printRewriteProof(
        use_cache, tp, rewrite, os, globalLetMap);
    break;

  default:
    for (size_t i = 0; i < rewrite->d_children.size(); i++) {
      callPrintRewriteProof(use_cache, tp, rewrite->d_children[i], os,
                            globalLetMap);
      std::cout << std::endl;
    }
    break;
  }
}

} /* CVC4 namespace */

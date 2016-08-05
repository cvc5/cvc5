// TODO: decide whether this should be part of rewriter_tables
#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "proof/theory_proof.h"
#include "theory/rewriter.h"
#include "util/proof.h"

namespace CVC4 {

void printProof(TheoryProofEngine *tp, const RewriteProof &rp, std::ostream &os,
                ProofLetMap &globalLetMap);

theory::RewriteResponse callPreRewriteWithProof(theory::TheoryId theory,
                                                TNode node,
                                                RewriteProof *proof);

theory::RewriteResponse callPostRewriteWithProof(theory::TheoryId theory,
                                                 TNode node,
                                                 RewriteProof *proof);

void callPrintRewriteProof(bool use_cache, TheoryProofEngine *tp,
                           const Rewrite *rewrite, std::ostream &os,
                           ProofLetMap &globalLetMap);

} /* CVC4 namespace */

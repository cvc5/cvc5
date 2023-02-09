/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database proof reconstructor
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__REWRITE_DB_PROOF_CONS__H
#define CVC5__THEORY__REWRITE_DB_PROOF_CONS__H

#include <map>

#include "expr/match_trie.h"
#include "expr/node.h"
#include "proof/method_id.h"
#include "proof/proof.h"
#include "proof/proof_generator.h"
#include "rewriter/basic_rewrite_rcons.h"
#include "rewriter/rewrite_db.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "theory/evaluator.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace rewriter {

/**
 * This class is used to reconstruct proofs of theory rewrites. It is described
 * in detail in the paper "Reconstructing Fine-Grained Proofs of Rewrites Using
 * a Domain-Specific Language", Noetzli et al FMCAD 2022.
 */
class RewriteDbProofCons : protected EnvObj
{
 public:
  RewriteDbProofCons(Env& env, RewriteDb* db);
  /**
   * Prove (= a b) with recursion limit recLimit. If cdp is provided, we add
   * a proof for this fact on it.
   */
  bool prove(CDProof* cdp,
             Node a,
             Node b,
             theory::TheoryId tid,
             MethodId mid,
             int64_t recLimit);

 private:
  /**
   * Basic utility for (user-independent) rewrite rule reconstruction. Handles
   * cases that should always be reconstructed, e.g. EVALUATE, REFL,
   * BETA_REDUCE.
   */
  BasicRewriteRCons d_trrc;
  /** Pointer to rewrite database */
  RewriteDb* d_db;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__REWRITE_DB_PROOF_CONS__H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Rewrite database proof reconstructor
 */

#include "rewriter/rewrite_db_proof_cons.h"


using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

RewriteDbProofCons::RewriteDbProofCons(Env& env, RewriteDb* db)
    : EnvObj(env),
      d_db(db)
{
}

bool RewriteDbProofCons::prove(CDProof* cdp,
                               Node a,
                               Node b,
                               theory::TheoryId tid,
                               MethodId mid,
                               uint32_t recLimit)
{
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal

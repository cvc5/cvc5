/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Methods for elaborating MACRO_BV_* proof rewrites.
 */

#include "theory/bv/macro_rewrite_elaborator.h"

#include "expr/aci_norm.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules_core.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

MacroRewriteElaborator::MacroRewriteElaborator(Env& env) : EnvObj(env) {}
MacroRewriteElaborator::~MacroRewriteElaborator() {}
bool MacroRewriteElaborator::ensureProofFor(CDProof* cdp,
                                            ProofRewriteRule id,
                                            const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Trace("bv-rew-elab") << "ensureProofFor: " << id << " " << eq << std::endl;
  // TODO PR #11676
  return false;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

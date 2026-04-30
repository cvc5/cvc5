/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lazy proof generator for the lia* arithmetic extension.
 */

#ifdef CVC5_USE_NORMALIZ

#include "theory/arith/liastar/liastar_proof_generator.h"

#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"
#include "proof/trust_id.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

LiaStarProofGenerator::LiaStarProofGenerator(Env& env, context::Context* c)
    : EnvObj(env), d_kind(c), d_aux(c)
{
}

void LiaStarProofGenerator::registerSplit(Node lemma, Node vectorPredicate)
{
  d_kind[lemma] = static_cast<uint32_t>(Kind::SPLIT);
  d_aux[lemma] = vectorPredicate;
}

void LiaStarProofGenerator::registerNonnegative(Node lemma, Node literal)
{
  d_kind[lemma] = static_cast<uint32_t>(Kind::NONNEGATIVE);
  d_aux[lemma] = literal;
}

void LiaStarProofGenerator::registerContainsReduce(Node lemma,
                                                   Node literal,
                                                   Node /*star*/)
{
  // `star` is recoverable as `lemma[1]` since `lemma == (= literal star)`.
  d_kind[lemma] = static_cast<uint32_t>(Kind::CONTAINS_REDUCE);
  d_aux[lemma] = literal;
}

bool LiaStarProofGenerator::hasProofFor(Node fact)
{
  return d_kind.find(fact) != d_kind.end();
}

std::shared_ptr<ProofNode> LiaStarProofGenerator::getProofFor(Node fact)
{
  auto it = d_kind.find(fact);
  Assert(it != d_kind.end())
      << "LiaStarProofGenerator::getProofFor: unknown fact " << fact;
  Info info;
  info.d_kind = static_cast<Kind>((*it).second);
  auto auxIt = d_aux.find(fact);
  Assert(auxIt != d_aux.end());
  info.d_aux = (*auxIt).second;
  switch (info.d_kind)
  {
    case Kind::SPLIT: return mkSplitProof(fact, info);
    case Kind::NONNEGATIVE: return mkNonnegativeProof(fact, info);
    case Kind::CONTAINS_REDUCE: return mkContainsReduceProof(fact, info);
  }
  Unreachable();
}

std::shared_ptr<ProofNode> LiaStarProofGenerator::mkSplitProof(Node lemma,
                                                               const Info& info)
{
  // (or vp (not vp))  via   ProofRule::SPLIT  with arg vp.
  CDProof cdp(d_env);
  cdp.addStep(lemma, ProofRule::SPLIT, {}, {info.d_aux});
  return cdp.getProofFor(lemma);
}

std::shared_ptr<ProofNode> LiaStarProofGenerator::mkNonnegativeProof(
    Node lemma, const Info& info)
{
  // The non-negativity lemma is only valid given the originating
  // STAR_CONTAINS literal. We emit a TRUST step with the literal as a
  // premise, making the proof shape structurally
  //   `STAR_CONTAINS(lambda, v) ⊢ (>= v_1 0) ∧ ... ∧ (>= v_n 0)`.
  // The TRUST tag remains until a real lia* proof is supplied (e.g. via
  // a subsolver call).
  CDProof cdp(d_env);
  cdp.addTrustedStep(
      lemma, TrustId::ARITH_LIA_STAR_NONNEGATIVE, {info.d_aux}, {});
  return cdp.getProofFor(lemma);
}

std::shared_ptr<ProofNode> LiaStarProofGenerator::mkContainsReduceProof(
    Node lemma, const Info& /*info*/)
{
  // Placeholder: lemma `(= literal star)` is taken on trust under a
  // lia*-specific TrustId. To replace with a subsolver proof, prove the
  // equivalence `literal <=> star` via a fresh subsolver and transcribe
  // its proof onto `getEnv().getProofNodeManager()` here.
  CDProof cdp(d_env);
  cdp.addTrustedStep(lemma, TrustId::ARITH_LIA_STAR_CONTAINS_REDUCE, {}, {});
  return cdp.getProofFor(lemma);
}

std::string LiaStarProofGenerator::identify() const
{
  return "LiaStarProofGenerator";
}

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5_USE_NORMALIZ */

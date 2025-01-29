/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Joerg Schurr, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays inference manager.
 */

#include "theory/arrays/inference_manager.h"

#include "options/smt_options.h"
#include "proof/trust_id.h"
#include "theory/builtin/proof_checker.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arrays {

InferenceManager::InferenceManager(Env& env, Theory& t, TheoryState& state)
    : TheoryInferenceManager(env, t, state, "theory::arrays::", false),
      d_lemmaPg(isProofEnabled() ? new EagerProofGenerator(
                    env, userContext(), "ArrayLemmaProofGenerator")
                                 : nullptr)
{
}

bool InferenceManager::assertInference(
    TNode atom, bool polarity, InferenceId id, TNode reason, ProofRule pfr)
{
  Trace("arrays-infer") << "TheoryArrays::assertInference: "
                        << (polarity ? Node(atom) : atom.notNode()) << " by "
                        << reason << "; " << id << std::endl;
  Assert(atom.getKind() == Kind::EQUAL);
  // if proofs are enabled, we determine which proof rule to add, otherwise
  // we simply assert the internal fact
  if (isProofEnabled())
  {
    Node fact = polarity ? Node(atom) : atom.notNode();
    std::vector<Node> children;
    std::vector<Node> args;
    // convert to proof rule application
    convert(pfr, fact, reason, children, args);
    return assertInternalFact(atom, polarity, id, pfr, children, args);
  }
  return assertInternalFact(atom, polarity, id, reason);
}

bool InferenceManager::arrayLemma(
    Node conc, InferenceId id, Node exp, ProofRule pfr, LemmaProperty p)
{
  Trace("arrays-infer") << "TheoryArrays::arrayLemma: " << conc << " by " << exp
                        << "; " << id << std::endl;
  NodeManager* nm = nodeManager();
  if (isProofEnabled())
  {
    std::vector<Node> children;
    std::vector<Node> args;
    // convert to proof rule application
    convert(pfr, conc, exp, children, args);
    // make the trusted lemma based on the eager proof generator and send
    TrustNode tlem = d_lemmaPg->mkTrustNode(conc, pfr, children, args);
    return trustedLemma(tlem, id, p);
  }
  // send lemma without proofs
  Node lem = nm->mkNode(Kind::IMPLIES, exp, conc);
  return lemma(lem, id, p);
}

void InferenceManager::convert(ProofRule& id,
                               Node conc,
                               Node exp,
                               std::vector<Node>& children,
                               std::vector<Node>& args)
{
  // note that children must contain something equivalent to exp,
  // regardless of the ProofRule.
  switch (id)
  {
    case ProofRule::MACRO_SR_PRED_INTRO:
      Assert(exp.isConst());
      args.push_back(conc);
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE:
      if (exp.isConst())
      {
        // Premise can be shown by rewriting, use standard predicate intro rule.
        // This is the case where we have 2 constant indices.
        id = ProofRule::MACRO_SR_PRED_INTRO;
        args.push_back(conc);
      }
      else
      {
        children.push_back(exp);
        args.push_back(conc[0]);
      }
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE_CONTRA:
      children.push_back(exp);
      break;
    case ProofRule::ARRAYS_READ_OVER_WRITE_1:
      Assert(exp.isConst());
      args.push_back(conc[0]);
      break;
    case ProofRule::ARRAYS_EXT:
      // since this rule depends on the ARRAY_DEQ_DIFF skolem which sorts
      // indices, we assert that the equality is ordered here, which it should
      // be based on the standard order for equality.
      Assert(exp.getKind() == Kind::NOT && exp[0].getKind() == Kind::EQUAL
             && exp[0][0] < exp[0][1]);
      children.push_back(exp);
      break;
    default:
      if (id != ProofRule::TRUST)
      {
        Assert(false) << "Unknown rule " << id << "\n";
      }
      children.push_back(exp);
      args.push_back(mkTrustId(nodeManager(), TrustId::THEORY_INFERENCE_ARRAYS));
      args.push_back(conc);
      id = ProofRule::TRUST;
      break;
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

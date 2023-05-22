/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arrays inference manager.
 */

#include "theory/arrays/inference_manager.h"

#include "options/smt_options.h"
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

bool InferenceManager::assertInference(TNode atom,
                                       bool polarity,
                                       InferenceId id,
                                       TNode reason,
                                       PfRule pfr)
{
  Trace("arrays-infer") << "TheoryArrays::assertInference: "
                        << (polarity ? Node(atom) : atom.notNode()) << " by "
                        << reason << "; " << id << std::endl;
  Assert(atom.getKind() == EQUAL);
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
    Node conc, InferenceId id, Node exp, PfRule pfr, LemmaProperty p)
{
  Trace("arrays-infer") << "TheoryArrays::arrayLemma: " << conc << " by " << exp
                        << "; " << id << std::endl;
  NodeManager* nm = NodeManager::currentNM();
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
  Node lem = nm->mkNode(IMPLIES, exp, conc);
  return lemma(lem, id, p);
}

void InferenceManager::convert(PfRule& id,
                               Node conc,
                               Node exp,
                               std::vector<Node>& children,
                               std::vector<Node>& args)
{
  // note that children must contain something equivalent to exp,
  // regardless of the PfRule.
  switch (id)
  {
    case PfRule::MACRO_SR_PRED_INTRO:
      Assert(exp.isConst());
      args.push_back(conc);
      break;
    case PfRule::ARRAYS_READ_OVER_WRITE:
      if (exp.isConst())
      {
        // Premise can be shown by rewriting, use standard predicate intro rule.
        // This is the case where we have 2 constant indices.
        id = PfRule::MACRO_SR_PRED_INTRO;
        args.push_back(conc);
      }
      else
      {
        children.push_back(exp);
        args.push_back(conc[0]);
      }
      break;
    case PfRule::ARRAYS_READ_OVER_WRITE_CONTRA: children.push_back(exp); break;
    case PfRule::ARRAYS_READ_OVER_WRITE_1:
      Assert(exp.isConst());
      args.push_back(conc[0]);
      break;
    case PfRule::ARRAYS_EXT: children.push_back(exp); break;
    default:
      if (id != PfRule::THEORY_INFERENCE)
      {
        Assert(false) << "Unknown rule " << id << "\n";
      }
      children.push_back(exp);
      args.push_back(conc);
      args.push_back(
          builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_ARRAYS));
      id = PfRule::THEORY_INFERENCE;
      break;
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace cvc5::internal

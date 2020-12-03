/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arrays inference manager
 **/

#include "theory/arrays/inference_manager.h"

#include "options/smt_options.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arrays {

InferenceManager::InferenceManager(Theory& t,
                                   TheoryState& state,
                                   ProofNodeManager* pnm)
    : TheoryInferenceManager(t, state, pnm),
      d_lemmaPg(pnm ? new EagerProofGenerator(pnm,
                                              state.getUserContext(),
                                              "ArrayLemmaProofGenerator")
                    : nullptr)
{
}

bool InferenceManager::assertInference(TNode atom,
                                       bool polarity,
                                       TNode reason,
                                       PfRule id)
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
    convert(id, fact, reason, children, args);
    return assertInternalFact(atom, polarity, id, children, args);
  }
  return assertInternalFact(atom, polarity, reason);
}

bool InferenceManager::arrayLemma(
    Node conc, Node exp, PfRule id, LemmaProperty p, bool doCache)
{
  Trace("arrays-infer") << "TheoryArrays::arrayLemma: " << conc << " by " << exp
                        << "; " << id << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  if (isProofEnabled())
  {
    std::vector<Node> children;
    std::vector<Node> args;
    // convert to proof rule application
    convert(id, conc, exp, children, args);
    // make the trusted lemma based on the eager proof generator and send
    TrustNode tlem = d_lemmaPg->mkTrustNode(conc, id, children, args);
    return trustedLemma(tlem, p, doCache);
  }
  // send lemma without proofs
  Node lem = nm->mkNode(IMPLIES, exp, conc);
  return lemma(lem, p, doCache);
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
      // unknown rule, should never happen
      Assert(false);
      children.push_back(exp);
      args.push_back(conc);
      id = PfRule::ARRAYS_TRUST;
      break;
  }
}

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

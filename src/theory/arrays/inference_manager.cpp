/*********************                                                        */
/*! \file inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
    : TheoryInferenceManager(t, state, pnm)
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
    switch (id)
    {
      case PfRule::MACRO_SR_PRED_INTRO: args.push_back(fact); break;
      case PfRule::ARRAYS_READ_OVER_WRITE_1:
        Assert(polarity);
        args.push_back(atom[0]);
        break;
      case PfRule::ARRAYS_READ_OVER_WRITE:
      case PfRule::ARRAYS_EXT:
      default:
        children.push_back(reason);
        args.push_back(fact);
        id = PfRule::ARRAYS_TRUST;
        break;
    }
    // note that children must contain something equivalent to reason,
    // regardless of the PfRule.
    return assertInternalFact(atom, polarity, id, children, args);
  }
  return assertInternalFact(atom, polarity, reason);
}

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

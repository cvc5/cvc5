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

bool InferenceManager::assertInference(TNode eq,
                                   bool polarity,
                                   TNode reason,
                                   PfRule r)
{
  Trace("arrays-infer") << "TheoryArrays::assertInference: "
                        << (polarity ? Node(eq) : eq.notNode()) << " by "
                        << reason << "; " << r << std::endl;
  Assert(eq.getKind() == EQUAL);
  if (options::proofNew())
  {
    Node fact = polarity ? Node(eq) : eq.notNode();
    std::vector<Node> args;
    switch (r)
    {
      case PfRule::MACRO_SR_PRED_INTRO: args.push_back(fact); break;
      case PfRule::ARRAYS_READ_OVER_WRITE_1:
        Assert(polarity);
        args.push_back(eq[0]);
        break;
      case PfRule::ARRAYS_READ_OVER_WRITE:
      case PfRule::ARRAYS_EXT:
      default:
        args.push_back(fact);
        r = PfRule::ARRAYS_TRUST;
        break;
    }
    // FIXME
    //return d_pfee->assertFact(fact, r, reason, args);
  }
  // FIXME
  return d_ee->assertEquality(eq, polarity, reason);
}

}  // namespace arrays
}  // namespace theory
}  // namespace CVC4

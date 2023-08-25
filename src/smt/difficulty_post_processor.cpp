/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for processing the difficulty of input assumptions
 * based on proof nodes.
 */

#include "smt/difficulty_post_processor.h"

#include "smt/env.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::theory;

namespace cvc5::internal {
namespace smt {

DifficultyPostprocessCallback::DifficultyPostprocessCallback()
    : d_currDifficulty(0)
{
}

bool DifficultyPostprocessCallback::setCurrentDifficulty(Node d)
{
  if (d.isConst() && d.getType().isInteger()
      && d.getConst<Rational>().sgn() >= 0
      && d.getConst<Rational>().getNumerator().fitsUnsignedInt())
  {
    d_currDifficulty = d.getConst<Rational>().getNumerator().toUnsignedInt();
    return true;
  }
  return false;
}

bool DifficultyPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 const std::vector<Node>& fa,
                                                 bool& continueUpdate)
{
  PfRule r = pn->getRule();
  if (r == PfRule::ASSUME)
  {
    Trace("difficulty-debug")
        << "  found assume: " << pn->getResult() << std::endl;
    d_accMap[pn->getResult()] += d_currDifficulty;
  }
  else if (r == PfRule::MACRO_SR_EQ_INTRO || r == PfRule::MACRO_SR_PRED_INTRO)
  {
    // premise is just a substitution, ignore
    continueUpdate = false;
    return false;
  }
  return true;
}

void DifficultyPostprocessCallback::getDifficultyMap(
    std::map<Node, Node>& dmap) const
{
  Assert(dmap.empty());
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, uint64_t>& d : d_accMap)
  {
    dmap[d.first] = nm->mkConstInt(Rational(d.second));
  }
}

}  // namespace smt
}  // namespace cvc5::internal

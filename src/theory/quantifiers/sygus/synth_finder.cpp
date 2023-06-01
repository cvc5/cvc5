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
 * Synthesis finder
 */

#include "theory/quantifiers/sygus/synth_finder.h"

#include "theory/quantifiers/sygus/

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

SynthFinder::SynthFinder(Env& env)
    : EnvObj(env),
      d_doRewSynth(false),
      d_doFilterLogicalStrength(false),
      d_use_sygus_type(false),
      d_tds(nullptr),
      d_crd(env,
            options().quantifiers.sygusRewSynthCheck,
            options().quantifiers.sygusRewSynthAccel,
            false),
      d_qg(nullptr),
      d_sols(env),
      d_sampler(env)
{
}

Node SynthFinder::findSynth(SynthFindTarget sft, const TypeNode& gtn)
{
  // should be a sygus datatype
  if (gtn.isNull() || !gtn.isDatatype() || !gtn.getDType().isSygus())
  {
    return Node::null();
  }
  NodeManager* nm = NodeManager::currentNM();
  // initialize the expression miner

  // initialize the enumerator
  Node e = nm->mkBoundVar(gtn);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

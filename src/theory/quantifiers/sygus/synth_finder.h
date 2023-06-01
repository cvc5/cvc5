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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYNTH_FINDER_H
#define CVC5__THEORY__QUANTIFIERS__SYNTH_FINDER_H

#include <cvc5/cvc5_types.h>

#include "theory/quantifiers/candidate_rewrite_database.h"
#include "theory/quantifiers/query_generator.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Algorithms for finding terms from sygus enumeration.
 */
class SynthFinder : protected EnvObj
{
 public:
  SynthFinder(Env& env);
  ~SynthFinder() {}
  /**
   * Find synth for the given target and provided grammar.
   */
  Node findSynth(SynthFindTarget sft, const TypeNode& gtn);

 private:
  /** candidate rewrite database */
  CandidateRewriteDatabase d_crd;
  /** The query generator we are using */
  std::unique_ptr<QueryGenerator> d_qg;
  /** sygus sampler object */
  SygusSampler d_sampler;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYNTH_FINDER_H */

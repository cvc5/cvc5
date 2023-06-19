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

#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class ExprMiner;
class ExprMinerId;
class SygusEnumeratorCallback;
class CandidateRewriteDatabase;
class QueryGenerator;
class RewriteVerifier;
class SygusSampler;
class SygusEnumerator;

/**
 * Algorithms for finding terms from sygus enumeration. This can be
 * seen as a wrapper around a (fast) sygus enumerator
 */
class SynthFinder : protected EnvObj
{
 public:
  SynthFinder(Env& env);
  ~SynthFinder() {}
  /**
   * Initialize find synth for the given target and provided grammar.
   */
  void initialize(modes::FindSynthTarget fst, const TypeNode& gtn);
  /**
   * Increment the enumerator of this class, returns false if the enumerator
   * is finished generating values.
   */
  bool increment();
  /**
   * Get the current found term based on the enumeration, or null if none
   * is available.
   */
  Node getCurrent();

 private:
  /** Initialize find synthesis target */
  void initializeInternal(modes::FindSynthTarget fst, const Node& e);
  /** Run find synthesis target */
  Node runNext(const Node& n, modes::FindSynthTarget fst);
  /** An identity expression miner */
  std::unique_ptr<ExprMinerId> d_eid;
  /** The enumerator callback */
  std::unique_ptr<SygusEnumeratorCallback> d_ecb;
  /** candidate rewrite database */
  std::unique_ptr<CandidateRewriteDatabase> d_crd;
  /** The query generator we are using */
  std::unique_ptr<QueryGenerator> d_qg;
  /** Rewrite verifier */
  std::unique_ptr<RewriteVerifier> d_rrv;
  /** sygus sampler object */
  std::unique_ptr<SygusSampler> d_sampler;
  /** The enumerator */
  std::unique_ptr<SygusEnumerator> d_enum;
  /** The active expression miner */
  ExprMiner* d_current;
  /** The current target we are given as input */
  modes::FindSynthTarget d_fst;
  /** The current target we are using */
  modes::FindSynthTarget d_fstu;
  /** The current buffer of terms returned by expression mining */
  std::vector<Node> d_buffer;
  /** The index in the buffer that is next to process */
  size_t d_bufferIndex;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__SYNTH_FINDER_H */

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
 * Management of current value for an enumerator
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_VALUE_MANAGER_H
#define CVC5__THEORY__QUANTIFIERS__SYGUS__ENUM_VALUE_MANAGER_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/enum_val_generator.h"
#include "theory/quantifiers/sygus/example_eval_cache.h"
#include "theory/quantifiers/sygus/sygus_enumerator_callback.h"
#include "theory/quantifiers/sygus_sampler.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersInferenceManager;
class TermRegistry;
class SygusStatistics;

/**
 * Management of current value for an enumerator. This class determines the
 * current value of an enumerator, which may be its model value if it is
 * not actively generated, or may be determined by the (fast) enumerator
 * when it is actively generated.
 */
class EnumValueManager : protected EnvObj
{
 public:
  EnumValueManager(Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   TermRegistry& tr,
                   SygusStatistics& s,
                   Node e,
                   bool hasExamples);
  ~EnumValueManager();
  /**
   * Get model value for term n. If n has a value that was excluded by
   * datatypes sygus symmetry breaking, this method returns null. It sets
   * activeIncomplete to true if the enumerator we are managing is
   * actively-generated, and its current value is null but it has not finished
   * generating values.
   */
  Node getEnumeratedValue(bool& activeIncomplete);
  /**
   * Notify that a synthesis candidate was tried, which clears the value
   * of d_evActiveGenWaiting, as well as the evaluation cache if modelSuccess
   * is true
   */
  void notifyCandidate(bool modelSuccess);
  /** Get the example evaluation cache */
  ExampleEvalCache* getExampleEvalCache();

 private:
  /**
   * Get model value for term n.
   */
  Node getModelValue(Node n);
  /** The enumerator */
  Node d_enum;
  /** Reference to the quantifiers state */
  QuantifiersState& d_qstate;
  /** Reference to the quantifiers inference manager */
  QuantifiersInferenceManager& d_qim;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  /** reference to the statistics of parent */
  SygusStatistics& d_stats;
  /** term database sygus of d_qe */
  TermDbSygus* d_tds;
  /** Sygus sampler (for --sygus-rr-verify) */
  std::unique_ptr<SygusSampler> d_samplerRrV;
  /** if we allocated a default sygus enumerator callback */
  std::unique_ptr<SygusEnumeratorCallback> d_secd;
  /** enumerator generators for each actively-generated enumerator */
  std::unique_ptr<EnumValGenerator> d_evg;
  /** example evaluation cache utility for each enumerator */
  std::unique_ptr<ExampleEvalCache> d_eec;
  /**
   * Map from enumerators to whether they are currently being
   * "actively-generated". That is, we are in a state where we have called
   * d_evg.addValue(v) for some v, and d_evg.getNext() has not yet
   * returned null. The range of this map stores the abstract value that
   * we are currently generating values from.
   */
  Node d_ev_curr_active_gen;
  /** the current waiting value of the actively-generated enumerator, if any
   *
   * This caches values that are actively generated and that we have not yet
   * passed to a call to SygusModule::constructCandidates. An example of when
   * this may occur is when there are two actively-generated enumerators e1 and
   * e2. Say on some iteration we actively-generate v1 for e1, the value
   * of e2 was excluded by symmetry breaking, and say the current master sygus
   * module does not handle partial models. Hence, we abort the current check.
   * We remember that the value of e1 was v1 by storing it here, so that on
   * a future check when v2 has a proper value, it is returned.
   */
  Node d_evActiveGenWaiting;
  /** the first value enumerated for the actively-generated enumerator
   *
   * This is to implement an optimization that only guards the blocking lemma
   * for the first value of an actively-generated enumerator.
   */
  Node d_evActiveGenFirstVal;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

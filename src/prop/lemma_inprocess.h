/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Learner for literals asserted at level zero.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LEMMA_INPROCESS_H
#define CVC5__PROP__LEMMA_INPROCESS_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "prop/cnf_stream.h"
#include "smt/env_obj.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

class ZeroLevelLearner;

/**
 * Lemma inprocess, which heuristically simplifies lemmas to an equivalent
 * form based on the current simplifications stored by the zero level learner.
 *
 * The intution of this class is to increase the likelihood that literals in the
 * SAT solver are reused. For example if a = 0 is learned at decision level
 * zero, and there is a SAT literal P(0), if P(a) is introduced as a new literal
 * in a lemma, we may replace it by P(0).
 *
 * As another example, if we learn a=b, c=b and we have a literal P(a), then
 * we may replace P(c) with P(a).
 *
 * This simplification is done selectively and will never replace a known SAT
 * literal by a new SAT literal. Further policies are determined by
 * lemma-inprocess-mode.
 *
 * Generally this method can only be applied to lemmas where the structure of
 * the lemma is not important. This includes quantifier instantiation lemmas
 * for example.
 */
class LemmaInprocess : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  LemmaInprocess(Env& env, CnfStream* cs, ZeroLevelLearner& zll);
  ~LemmaInprocess() {}
  /** Inprocess lemma */
  TrustNode inprocessLemma(TrustNode& trn);

 private:
  /**
   * Process internal, returns an equivalent formula to lem, assuming d_tsmap.
   */
  Node processInternal(const Node& lem);
  /** Pointer to CNF stream */
  CnfStream* d_cs;
  /** Reference to the current available simplification */
  theory::TrustSubstitutionMap& d_tsmap;
  /** Mapping from simplified literals to a known SAT literal */
  context::CDHashMap<Node, Node> d_subsLitMap;
  /** Equivalent literal lemmas we have sent */
  context::CDHashSet<Node> d_eqLitLemmas;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif

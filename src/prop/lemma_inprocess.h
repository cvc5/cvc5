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
 * Learner for literals asserted at level zero.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__LEMMA_INPROCESS_H
#define CVC5__PROP__LEMMA_INPROCESS_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/trust_substitutions.h"
#include "prop/cnf_stream.h"

namespace cvc5::internal {

class TheoryEngine;

namespace prop {

class ZeroLevelLearner;
/**
 * Lemma inprocess
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
  /** Process internal */
  Node processInternal(const Node& lem);
  /** Pointer to CNF stream */
  CnfStream* d_cs;
  /** Substitution */
  theory::TrustSubstitutionMap& d_tsmap;
  /** Substitution */
  theory::TrustSubstitutionMap& d_tcpmap;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif

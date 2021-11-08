/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Class for verifying queries for synthesis solutions
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__SYNTH_VERIFY_H
#define CVC5__THEORY__QUANTIFIERS__SYNTH_VERIFY_H

#include <memory>

#include "options/options.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"
#include "util/result.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

/**
 * Class for verifying queries corresponding to synthesis conjectures
 */
class SynthVerify : protected EnvObj
{
 public:
  SynthVerify(Env& env, TermDbSygus* tds);
  ~SynthVerify();
  /**
   * Verification call, which takes into account specific aspects of the
   * synthesis conjecture, e.g. recursive function definitions.
   *
   * @param query The query corresponding to the negated body of the synthesis
   * conjecture
   * @param vars The skolem variables witnessing the counterexample
   * @param mvs If satisfiable, these contain the model value for vars
   * @return The result of whether query is satisfiable.
   */
  Result verify(Node query,
                const std::vector<Node>& vars,
                std::vector<Node>& mvs);

 private:
  /** Pointer to the term database sygus */
  TermDbSygus* d_tds;
  /** The options for subsolver calls */
  Options d_subOptions;
  /** The logic info for subsolver calls */
  const LogicInfo& d_subLogicInfo;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif

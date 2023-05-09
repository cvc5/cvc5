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

namespace cvc5::internal {
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
  /**
   * Same as above, without getting a model.
   */
  Result verify(Node query);

 private:
  /**
   * Preprocess query internal. This returns the rewritten form of query
   * and includes all relevant function definitions, i.e. those that occur
   * in query. These are added as top-level conjuncts to the returned formula.
   *
   * For each oracle function f in the query, we conjoin equalities f(c) = d
   * where (c, d) is an I/O pair obtained for a call to a oracle. In contrast
   * to the description in Polgreen et al VMCAI 2022, the verification subcall
   * uses SMT, not SMTO. Instead f is treated as an ordinary function symbol,
   * and its current I/O pairs are communicated explicitly via these conjuncts.
   */
  Node preprocessQueryInternal(Node query);
  /** Pointer to the term database sygus */
  TermDbSygus* d_tds;
  /** The options for subsolver calls */
  Options d_subOptions;
  /** The logic info for subsolver calls */
  const LogicInfo& d_subLogicInfo;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif

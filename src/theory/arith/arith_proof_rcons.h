/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A generic utility for inferring proofs for arithmetic lemmas.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H
#define CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H

#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_id.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
class TConvProofGenerator;
namespace theory {
namespace arith {
class ArithSubs;

/**
 * Proof generator that is used for reconstructing lemmas coming from
 * arithmetic that do not have proof tracking. This includes:
 * - ARITH_DIO_LEMMA, lemmas coming from the dio solver.
 */
class ArithProofRCons : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   * @param id The trust id to use if the proof reconstruction fails.
   */
  ArithProofRCons(Env& env, TrustId id);
  virtual ~ArithProofRCons();
  /**
   * Get proof for an arithmetic lemma. Based on the trust id of this class,
   * we infer the proof for fact.
   *
   * For example, if d_id is ARITH_DIO_LEMMA, then we use a procedure which
   * infers entailed equalities from the disjuncts of the lemma and applies
   * substitution+rewriting to prove the remainder of the lemma. For example,
   * given:
   * (not (and (>= x 2)) (<= x 2) (< x 0))
   * We skeleton of the proof looks like:
   *              -------- --------
   *              (>= x 2) (<= x 2)
   * -------      ----------------- via trichotomy
   * (< x 0)      (= x 2)
   * --------------------- MACRO_SR_PRED_TRANSFORM
   * false
   * ------------------------------------- SCOPE
   * (not (and (>= x 2)) (<= x 2) (< x 0))
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;

 private:
  /**
   * If returns true, then as is equivalent to an equality (= x t). We do
   * the following:
   * (1) Add a proof of (= x t) with free assumption as to cdp.
   * (2) Add a rewrite step x --> t to tconv referencing cdp.
   * (3) Apply the substitution x --> t to the range of asubs and add x --> t
   * to it.
   */
  bool solveEquality(CDProof& cdp,
                     TConvProofGenerator& tconv,
                     ArithSubs& asubs,
                     const Node& as);
  /**
   * Returns the result of applying asubs to a and then rewriting.
   */
  Node applySR(ArithSubs& asubs, const Node& a);
  /**
   * Returns the result of applying asubs to a and then rewriting, where a
   * is a predicate. Furthermore ensures that a proof of the returned predicate
   * is added to cdp with free assumption a. Note that if we return a unchanged,
   * then no proof is added to cdp.
   */
  Node applySR(CDProof& cdp,
               TConvProofGenerator& tcnv,
               ArithSubs& asubs,
               const Node& a);
  /** The trust id to use if the proof reconstruction fails. */
  TrustId d_id;
  /** False node */
  Node d_false;
};

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H */

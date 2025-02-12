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
 * A utility for converting proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__SUBTYPE_ELIM_PROOF_CONVERTER_H
#define CVC5__PROOF__SUBTYPE_ELIM_PROOF_CONVERTER_H

#include "expr/node.h"
#include "expr/subtype_elim_node_converter.h"
#include "proof/proof_node_converter.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofChecker;

/**
 * A callback class for converting proofs to those that do not involve
 * mixed arithmetic. We update all proofs proving F to those proving
 * d_nconv.convert(F), where d_nconv is the utility that eliminates mixed
 * arithmetic from F. Moreover all arguments t in proof nodes are
 * d_nconv.convert(t).
 */
class SubtypeElimConverterCallback : public ProofNodeConverterCallback,
                                     protected EnvObj
{
 public:
  SubtypeElimConverterCallback(Env& env);
  virtual ~SubtypeElimConverterCallback() {}
  /**
   * This converts all proofs of formulas F to proofs of d_nconv.convert(F),
   * where d_nconv is the utility that eliminates mixed arithmetic from F.
   *
   * To do this, we typically just apply the original proof rule to the
   * converted children, which should always succeed in proving a new formula
   * F'. If F' is not syntactically equal to d_nconv.convert(F), then we
   * correct it, which is necessary in several cases:
   * (1) congruence,
   * (2) arithmetic mul pos/neg,
   * (3) arithmetic summation,
   * (4) instantiation,
   * (5) MACRO_SR_EQ_INTRO.
   * For these cases, we typically use the prove submethod below to prove a
   * lifting of proofs from integer predicates to real predicates and retry
   * the original proof rule.
   */
  Node convert(Node res,
               ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               CDProof* cdp) override;

 private:
  /**
   * Try to prove expected via the given rule, children, and arguments. Return
   * true if this proves expected, otherwise we return false and set newRes
   * to what was proven by (id, children, args).
   *
   * If we return true, we add the step (id, children, args) to cdp.
   */
  bool tryWith(ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node expected,
               Node& newRes,
               CDProof* cdp);
  /**
   * Prove, which attempts to prove tgt from src, where:
   * - src is an arithmetic predicate of the form (~ t s),
   * - tgt is an arithmetic predicate of the form (~ t' s') where t' (resp. s)
   * is semantically equal to (to_real t) (resp. (to_real s)).
   * Returns true if we succeed to prove tgt, where we add a proof of tgt to
   * cdp whose free assumption is src.
   */
  bool prove(const Node& src, const Node& tgt, CDProof* cdp);
  /** The node converter */
  SubtypeElimNodeConverter d_nconv;
  /** The proof checker we are using */
  ProofChecker* d_pc;
};

}  // namespace cvc5::internal

#endif

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
 * Proof logger utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_LOGGER_H
#define CVC5__SMT__PROOF_LOGGER_H

#include "proof/alf/alf_node_converter.h"
#include "proof/alf/alf_printer.h"
#include "proof/proof_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace smt {
class Assertions;
class PfManager;
class ProofPostprocess;
}  // namespace smt

/**
 */
class ProofLogger : protected EnvObj
{
 public:
  /** */
  ProofLogger(Env& env,
              std::ostream& out,
              smt::PfManager* pm,
              smt::Assertions& as,

              smt::ProofPostprocess* ppp);
  ~ProofLogger();
  /**
   * @param input The list of input clauses after preprocessing and conversion
   * to CNF.
   */
  virtual void logCnfPreprocessInputs(const std::vector<Node>& inputs);
  /**
   * @param pfns proofs of the preprocessed inputs. The free assumptions of
   * proofs in pfns are the preprocessed input formulas. If preprocess proofs
   * are avialable, this method connects pfn to the original input formulas.
   */
  void logCnfPreprocessInputProofs(
      std::vector<std::shared_ptr<ProofNode>>& pfns);
  /**
   * @param n Called when the clause n is added to the SAT solver, where n is
   * (the CNF conversion of) a theory lemma.
   */
  virtual void logTheoryLemma(const Node& n);
  /**
   * @param n Called when the clause n is added to the SAT solver, where pfn
   * is a closed proof of (the CNF conversion of) a theory lemma.
   */
  void logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn);
  /**
   * Called when the SAT solver derives false.
   * @param inputs The input clauses notified above.
   * @param lemmas The list of theory lemmas notified above.
   */
  virtual void logSatRefutation();

  /**
   * Called when the SAT solver generates a proof of false. The free assumptions
   * of this proof is the union of the CNF conversion of input and theory lemmas
   * as notified above.
   * @param pfn The refutation proof.
   */
  void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn);

 private:
  smt::PfManager* d_pm;
  ProofNodeManager* d_pnm;
  smt::Assertions& d_as;
  smt::ProofPostprocess* d_ppp;
  proof::AlfNodeConverter d_atp;
  proof::AlfPrinter d_alfp;
  proof::AlfPrintChannelOut d_aout;
  /** */
  std::shared_ptr<ProofNode> d_ppProof;
  /** */
  std::vector<std::shared_ptr<ProofNode>> d_lemmaPfs;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */

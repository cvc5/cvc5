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
  void logCnfPreprocessInputs(const std::vector<Node>& inputs);
  /**
   * pfn is a proof of a conjunction (and F1 ... Fn) where F1 ... Fn is the
   * CNF of the input formulas.
   * The free assumptions of pfn are the preprocessed input formulas.
   * This method connects pfn to the original input formulas and prints it.
   */
  void logCnfPreprocessInputProofs(
      std::vector<std::shared_ptr<ProofNode>>& pfns);
  /** */
  void logTheoryLemma(const Node& n);
  /** */
  void logTheoryLemmaProof(std::shared_ptr<ProofNode>& pfn);
  /** */
  void logSatRefutation(const std::vector<Node>& inputs,
                        const std::vector<Node>& lemmas);
  /** */
  void logSatRefutationProof(std::shared_ptr<ProofNode>& pfn);

 private:
  std::ostream& d_out;
  smt::PfManager* d_pm;
  ProofNodeManager* d_pnm;
  smt::Assertions& d_as;
  smt::ProofPostprocess* d_ppp;
  proof::AlfNodeConverter d_atp;
  proof::AlfPrinter d_alfp;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */

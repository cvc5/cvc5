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
}

/**
 */
class ProofLogger : protected EnvObj
{
 public:
  /** */
  ProofLogger(Env& env, smt::PfManager* pm, smt::Assertions& as);
  ~ProofLogger();
  /** */
  void logClause(std::shared_ptr<ProofNode>& pfn);
  /** */
  void logClauseFromPreprocessedInput(std::shared_ptr<ProofNode>& pfn);
  /** */
  void logTheoryLemma(const Node& n);

 private:
  smt::PfManager* d_pm;
  smt::Assertions& d_as;
  proof::AlfNodeConverter d_atp;
  proof::AlfPrinter d_alfp;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */

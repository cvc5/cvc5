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

#ifndef CVC5__PROOF__PROOF_LOGGER_H
#define CVC5__PROOF__PROOF_LOGGER_H

#include "smt/env_obj.h"
#include "proof/proof_node.h"
#include "proof/alf/alf_node_converter.h"
#include "proof/alf/alf_printer.h"

namespace cvc5::internal {

namespace rewriter {
class RewriteDb;
}
/**
 */
class ProofLogger : protected EnvObj
{
 public:
  /** */
  ProofLogger(Env& env, rewriter::RewriteDb* rdb);
  ~ProofLogger();
  /** */
  void logInputClause(std::shared_ptr<ProofNode>& pfn);
  /** */
  void logTheoryLemma(const Node& n);
private:
  proof::AlfNodeConverter d_atp;
  proof::AlfPrinter d_alfp;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__PROOF_LOGGER_H */

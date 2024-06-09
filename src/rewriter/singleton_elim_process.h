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
 * Rewrite database singleton elimination converter.
 */

#include "cvc5_private.h"

#ifndef CVC5__REWRITER__SINGLETON_ELIM_PROCESS__H
#define CVC5__REWRITER__SINGLETON_ELIM_PROCESS__H

#include <cvc5/cvc5_proof_rule.h>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "proof/conv_proof_generator.h"
#include "proof/proof.h"

namespace cvc5::internal {
namespace rewriter {

/**  */
class SingletonElimConverter
{
 public:
  SingletonElimConverter(Env& env);
  /**
   * Return the proof of (= n nse) where nse is the result of eliminating
   * singletons from n.
   */
  std::shared_ptr<ProofNode> convert(const Node& n, const Node& nse);

 private:
  /** A TConvProofGenerator */
  TConvProofGenerator d_tpg;
};

}  // namespace rewriter
}  // namespace cvc5::internal

#endif /* CVC5__REWRITER__SINGLETON_ELIM_PROCESS__H */

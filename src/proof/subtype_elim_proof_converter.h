/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
 * A virtual callback class for converting ProofNode.
 */
class SubtypeElimConverterCallback : public ProofNodeConverterCallback,
                                     protected EnvObj
{
 public:
  SubtypeElimConverterCallback(Env& env);
  virtual ~SubtypeElimConverterCallback() {}
  /**
   * Update the proof rule application, store steps in cdp. Return true if
   * the proof changed. It can be assumed that cdp contains proofs of each
   * fact in children.
   *
   * Returns the desired conclusion of this step
   */
  Node convert(Node res,
               ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               CDProof* cdp) override;

 private:
  /** Try with */
  bool tryWith(ProofRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               Node resc,
               Node& newRes,
               CDProof* cdp);
  /** The node converter */
  SubtypeElimNodeConverter d_nconv;
  /** The proof checker we are using */
  ProofChecker* d_pc;
};

}  // namespace cvc5::internal

#endif

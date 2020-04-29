/*********************                                                        */
/*! \file lazy_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__LAZY_PROOF_H
#define CVC4__EXPR__LAZY_PROOF_H

#include <map>
#include <vector>

#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "theory/proof_generator.h"

namespace CVC4 {

/**
 * A (context-dependent) lazy proof.
 */
class LazyCDProof : public CDProof
{
 public:
  LazyCDProof(ProofNodeManager* pnm, context::Context* c = nullptr);
  ~LazyCDProof();
  /**
   * Get lazy proof for fact, or nullptr if it does not exist. This may
   * additionally proof generators to generate proofs for ASSUME nodes that
   * don't yet have a concrete proof.
   */
  std::shared_ptr<ProofNode> getLazyProof(Node fact);
  /** Add step by generator 
   * 
   * This asserts that expected can be proven by proof generator pg if
   * it is required to do so.
   */
  void addStep(Node expected, ProofGenerator * pg, bool forceOverwrite=false);
 protected:
  /** Maps facts that can be proven to generators */
  std::map< Node, ProofGenerator * > d_gens;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__LAZY_PROOF_H */

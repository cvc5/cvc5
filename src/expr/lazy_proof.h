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

#include <unordered_map>
#include <vector>

#include "expr/proof.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"

namespace CVC4 {

/**
 * A (context-dependent) lazy proof.
 */
class LazyCDProof : public CDProof
{
 public:
  LazyCDProof(ProofNodeManager* pnm,
              ProofGenerator* dpg = nullptr,
              context::Context* c = nullptr);
  ~LazyCDProof();
  /**
   * Get lazy proof for fact, or nullptr if it does not exist. This may
   * additionally proof generators to generate proofs for ASSUME nodes that
   * don't yet have a concrete proof.
   */
  std::shared_ptr<ProofNode> mkProof(Node fact) override;
  /** Add step by generator
   *
   * This asserts that expected can be proven by proof generator pg if
   * it is required to do so.
   */
  void addLazyStep(Node expected,
                   ProofGenerator* pg,
                   bool forceOverwrite = false);
  /** Does this have any proof generators? */
  bool hasGenerators() const;
  /** Does the given fact have a generator? */
  bool hasGenerator(Node fact) const;

 protected:
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGeneratorMap;
  /** Maps facts that can be proven to generators */
  NodeProofGeneratorMap d_gens;
  /** The default proof generator */
  ProofGenerator* d_defaultGen;
  /** Get generator for fact, or nullptr if it doesnt exist */
  ProofGenerator* getGeneratorFor(Node fact, bool& isSym);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__LAZY_PROOF_H */

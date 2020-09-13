/*********************                                                        */
/*! \file lazy_proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
 * A (context-dependent) lazy proof. This class is an extension of CDProof
 * that additionally maps facts to proof generators in a context-dependent
 * manner. It extends CDProof with an additional method, addLazyStep for adding
 * steps to a proof via a given proof generator.
 */
class LazyCDProof : public CDProof
{
 public:
  /** Constructor
   *
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param dpg The (optional) default proof generator, which is called
   * for facts that have no explicitly provided generator.
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   */
  LazyCDProof(ProofNodeManager* pnm,
              ProofGenerator* dpg = nullptr,
              context::Context* c = nullptr,
              std::string name = "LazyCDProof");
  ~LazyCDProof();
  /**
   * Get lazy proof for fact, or nullptr if it does not exist. This may
   * additionally call proof generators to generate proofs for ASSUME nodes that
   * don't yet have a concrete proof.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Add step by generator
   *
   * This method stores that expected can be proven by proof generator pg if
   * it is required to do so. This mapping is maintained in the remainder of
   * the current context (according to the context c provided to this class).
   *
   * It is important to note that pg is asked to provide a proof for expected
   * only when no other call for the fact expected is provided via the addStep
   * method of this class. In particular, pg is asked to prove expected when it
   * appears as the conclusion of an ASSUME leaf within CDProof::getProofFor.
   *
   * @param expected The fact that can be proven.
   * @param pg The generator that can proof expected.
   * @param isClosed Whether to expect that pg can provide a closed proof for
   * this fact.
   * @param ctx The context we are in (for debugging).
   * @param forceOverwrite If this flag is true, then this call overwrites
   * an existing proof generator provided for expected, if one was provided
   * via a previous call to addLazyStep in the current context.
   * @param trustId If a null proof generator is provided, we add a step to
   * the proof that has trustId as the rule and expected as the sole argument.
   * We do this only if trustId is not PfRule::ASSUME. This is primarily used
   * for identifying the kind of hole when a proof generator is not given.
   */
  void addLazyStep(Node expected,
                   ProofGenerator* pg,
                   bool isClosed = true,
                   const char* ctx = "LazyCDProof::addLazyStep",
                   bool forceOverwrite = false,
                   PfRule trustId = PfRule::ASSUME);
  /**
   * Does this have any proof generators? This method always returns true
   * if the default is non-null.
   */
  bool hasGenerators() const;
  /** Does the given fact have an explicitly provided generator? */
  bool hasGenerator(Node fact) const;

 protected:
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGeneratorMap;
  /** Maps facts that can be proven to generators */
  NodeProofGeneratorMap d_gens;
  /** The default proof generator */
  ProofGenerator* d_defaultGen;
  /**
   * Get generator for fact, or nullptr if it doesnt exist. This method is
   * robust to symmetry of (dis)equality. It updates isSym to true if a
   * proof generator for the symmetric form of fact was provided.
   */
  ProofGenerator* getGeneratorFor(Node fact, bool& isSym);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__LAZY_PROOF_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lazy proof utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__LAZY_PROOF_H
#define CVC5__PROOF__LAZY_PROOF_H

#include "context/cdhashset.h"
#include "proof/proof.h"

namespace cvc5::internal {

class ProofGenerator;
class ProofNodeManager;

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
   * @param name The name of this proof generator (for debugging)
   * @param autoSym Whether symmetry steps are automatically added when adding
   * steps to this proof
   * @param doCache Whether the proofs we process in getProofFor are cached
   * based on the context of this class. In other words, we assume that the
   * subproofs returned by getProofFor are not re-processed on repeated calls
   * to getProofFor, even if new steps are provided to this class in the
   * meantime.
   */
  LazyCDProof(Env& env,
              ProofGenerator* dpg = nullptr,
              context::Context* c = nullptr,
              const std::string& name = "LazyCDProof",
              bool autoSym = true,
              bool doCache = true);
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
   * @param trustId If a null proof generator is provided, we add a step to
   * the proof that has trustId as the rule and expected as the sole argument.
   * We do this only if trustId is not PfRule::ASSUME. This is primarily used
   * for identifying the kind of hole when a proof generator is not given.
   * @param isClosed Whether to expect that pg can provide a closed proof for
   * this fact.
   * @param ctx The context we are in (for debugging).
   * @param forceOverwrite If this flag is true, then this call overwrites
   * an existing proof generator provided for expected, if one was provided
   * via a previous call to addLazyStep in the current context.
   */
  void addLazyStep(Node expected,
                   ProofGenerator* pg,
                   PfRule trustId = PfRule::ASSUME,
                   bool isClosed = false,
                   const char* ctx = "LazyCDProof::addLazyStep",
                   bool forceOverwrite = false);
  /**
   * Does this have any proof generators? This method always returns true
   * if the default is non-null.
   */
  bool hasGenerators() const;
  /** Does the given fact have an explicitly provided generator? */
  bool hasGenerator(Node fact) const;

 protected:
  typedef context::CDHashMap<Node, ProofGenerator*> NodeProofGeneratorMap;
  typedef context::CDHashSet<ProofNode*> ProofNodeSet;
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
  /** whether d_allVisited is maintained */
  bool d_doCache;
  /** The set of proof nodes we have processed in getProofFor */
  ProofNodeSet d_allVisited;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__LAZY_PROOF_H */

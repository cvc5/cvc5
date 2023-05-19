/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lazy proof chain utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__LAZY_PROOF_CHAIN_H
#define CVC5__PROOF__LAZY_PROOF_CHAIN_H

#include <vector>

#include "proof/proof.h"

namespace cvc5::internal {

class ProofNodeManager;

/**
 * A (context-dependent) lazy generator for proof chains. This class is an
 * extension of ProofGenerator that additionally that maps facts to proof
 * generators in a context-dependent manner. The map is built with the addition
 * of lazy steps mapping facts to proof generators. More importantly, its
 * getProofFor method expands the proof generators registered to this class by
 * connecting, for the proof generated to one fact, assumptions to the proofs
 * generated for those assumptinos that are registered in the chain.
 */
class LazyCDProofChain : public CDProof
{
 public:
  /** Constructor
   *
   * @param env Reference to the environment
   * @param cyclic Whether this instance is robust to cycles in the chain.
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   * @param defGen The default generator to be used if no generator exists
   * for a step.
   * @param defRec Whether this instance expands proofs from defGen recursively.
   */
  LazyCDProofChain(Env& env,
                   bool cyclic = true,
                   context::Context* c = nullptr,
                   ProofGenerator* defGen = nullptr,
                   bool defRec = true,
                   const std::string& name = "LazyCDProofChain");
  ~LazyCDProofChain();
  /**
   * Get lazy proof for fact, or nullptr if it does not exist, by connecting the
   * proof nodes generated for each intermediate relevant fact registered in the
   * chain (i.e., in the domain of d_gens).
   *
   * For example, if d_gens consists of the following pairs
   *
   * --- (A, PG1)
   * --- (B, PG2)
   * --- (C, PG3)
   *
   * and getProofFor(A) is called, with PG1 generating a proof with assumptions
   * B and D, then B is expanded, with its assumption proof node being updated
   * to the expanded proof node, while D is not. Assuming PG2 provides a proof
   * with assumptions C and E, then C is expanded and E is not. Suppose PG3
   * gives a closed proof, thus the call getProofFor(A) produces a proof node
   *
   *  A : ( ... B : ( ... C : (...), ... ASSUME( E ) ), ... ASSUME( D ) )
   *
   * Note that the expansions are done directly on the proof nodes produced by
   * the generators.
   *
   * If this instance has been set to be robust to cyclic proofs (i.e., d_cyclic
   * is true), then the construction of the proof chain checks that there are no
   * cycles, i.e., a given fact would have itself as an assumption when
   * connecting the chain links. If such a cycle were to be detected then the
   * fact will be marked as an assumption and not expanded in the final proof
   * node. The method does not fail.
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
   * Moreover the lazy steps of this class are expected to fulfill the
   * requirement that pg.getProofFor(expected) generates a proof node closed
   * with relation to
   *  (1) a fixed set F1, ..., Fn,
   *  (2) formulas in the current domain of d_gens.
   *
   * This is so that we only add links to the chain that depend on a fixed set
   * of assumptions or in other links.
   *
   * @param expected The fact that can be proven.
   * @param pg The generator that can proof expected.
   * @param assumptions The fixed set of assumptions with relation to which the
   * chain, now augmented with expect, must be closed.
   * @param ctx The context we are in (for debugging).
   */
  void addLazyStep(Node expected,
                   ProofGenerator* pg,
                   const std::vector<Node>& assumptions,
                   const char* ctx = "LazyCDProofChain::addLazyStep");

  /** As above but does not do the closedness check. */
  void addLazyStep(Node expected, ProofGenerator* pg);

  /** Does the given fact have an explicitly provided generator? */
  bool hasGenerator(Node fact) const;

  /**
   * Get generator for fact, or nullptr if it doesnt exist.
   */
  ProofGenerator* getGeneratorFor(Node fact);

  /** identify */
  std::string identify() const override;

  /** Retrieve, for each fact in d_gens, it mapped to the proof node generated
   * by its generator in d_gens.  */
  const std::map<Node, std::shared_ptr<ProofNode>> getLinks() const;

 private:
  /**
   * Get generator for fact, or nullptr if it doesnt exist. Updates rec to
   * true if we should recurse on its proof.
   */
  ProofGenerator* getGeneratorForInternal(Node fact, bool& rec);
  /**
   * Get internal proof for fact from the underlying CDProof, if any, otherwise
   * via a call to the above method.
   *
   * Returns a nullptr when no internal proof stored.
   */
  std::shared_ptr<ProofNode> getProofForInternal(Node fact, bool& rec);
  /** Whether this instance is robust to cycles in the chain. */
  bool d_cyclic;
  /** Whether we expand recursively (for the default generator) */
  bool d_defRec;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** Maps facts that can be proven to generators */
  context::CDHashMap<Node, ProofGenerator*> d_gens;
  /** The default proof generator (if one exists) */
  ProofGenerator* d_defGen;
  /** Name (for debugging) */
  std::string d_name;
};

}  // namespace cvc5::internal

#endif /* CVC5__PROOF__LAZY_PROOF_CHAIN_H */

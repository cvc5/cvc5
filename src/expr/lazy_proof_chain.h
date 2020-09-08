/*********************                                                        */
/*! \file lazy_proof_chain.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy proof chain utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__LAZY_PROOF_CHAIN_H
#define CVC4__EXPR__LAZY_PROOF_CHAIN_H

#include <unordered_map>
#include <vector>

#include "expr/proof.h"
#include "expr/proof_generator.h"
#include "expr/proof_node_manager.h"

namespace CVC4 {

/**
 * A (context-dependent) lazy proof chain. This class is an extension of CDProof
 * that additionally maps facts to proof generators in a context-dependent
 * manner. It extends CDProof with an additional method, addLazyStep for adding
 * steps to a proof via a given proof generator. More importantly, its
 * getProofFor method is so that it expands the proof generators registered to
 * this class until a fix-point.
 */
class LazyCDProofChain : public CDProof
{
 public:
  /** Constructor
   *
   * @param pnm The proof node manager for constructing ProofNode objects.
   * @param c The context that this class depends on. If none is provided,
   * this class is context-independent.
   */
  LazyCDProofChain(ProofNodeManager* pnm,
                   context::Context* c = nullptr,
                   std::string name = "LazyCDProofChain");
  ~LazyCDProofChain();
  /**
   * Get lazy proof for fact, or nullptr if it does not exist. This may
   * additionally call proof generators to generate proofs for ASSUME nodes that
   * don't yet have a concrete proof. This is done until a fix-point, so that
   * the nods registered in d_gens are connected in a chain.
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
   * requirement that pg.getProofFor(expected) triggers proof generators
   * registered to this class (to the leaves of the initial proof of expected)
   * until a fix point, building a chain of connections so that the final
   * assumption leaves are contained in
   *  (1) a fixed set F1, ..., Fn,
   *  (2) formulas in the current domain of d_gens.
   *
   * As a precondition for adding a step, we require:
   *  (1) F is not already in the domain of this map. (HB Not sure about this
   * one) (2) F does not occur in F1 ... Fn.
   *
   * @param expected The fact that can be proven.
   * @param pg The generator that can proof expected.
   * @param ctx The context we are in (for debugging).
   */
  void addLazyStep(Node expected,
                   ProofGenerator* pg,
                   const char* ctx = "LazyCDProofChain::addLazyStep");
  /**
   * Does this have any proof generators? This method always returns true
   * if the default is non-null.
   */
  bool hasGenerators() const;
  /** Does the given fact have an explicitly provided generator? */
  bool hasGenerator(Node fact) const;

  /**
   * Get generator for fact, or nullptr if it doesnt exist. This method is
   * robust to symmetry of (dis)equality. It updates isSym to true if a
   * proof generator for the symmetric form of fact was provided.
   */
  ProofGenerator* getGeneratorFor(Node fact, bool& isSym);

  /** Sets the fixed set of assumptions on which this chain depends. This is
   * used for debugging purposes when checking that added steps are closed. */
  void addFixedAssumptions(const std::vector<Node>& assumptions);

  /** as above, but single assumption */
  void addFixedAssumption(Node assumption);

 protected:
  typedef context::CDHashMap<Node, ProofGenerator*, NodeHashFunction>
      NodeProofGeneratorMap;
  /** Maps facts that can be proven to generators */
  NodeProofGeneratorMap d_gens;

  std::vector<Node> d_fixedAssumptions;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__LAZY_PROOF_CHAIN_H */

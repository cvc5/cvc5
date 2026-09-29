/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lambda lifting
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__LAMBDA_LIFT_H
#define CVC5__THEORY__UF__LAMBDA_LIFT_H

#include <map>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/skolem_lemma.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/**
 * Module for doing various operations on lambdas, including lambda lifting.
 *
 * Lambdas that are lifted are replaced by a skolem k during preprocessing,
 * where the lemma forall x. (k x) = (lam x) is added. By default
 * (--uf-lazy-ll), we only lift lambdas that may induce circular dependencies
 * in model construction (see needsLift). Other lambdas occur directly in
 * constraints, and are beta-reduced on demand by the higher-order extension
 * when they are equated to ordinary functions. With --no-uf-lazy-ll, all
 * lambdas are lifted.
 */
class LambdaLift : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;

 public:
  LambdaLift(Env& env);

  /**
   * This method has the same contract as Theory::ppRewrite.
   * Preprocess, return the trust node corresponding to the rewrite. A null
   * trust node indicates no rewrite.
   */
  TrustNode ppRewrite(Node node, std::vector<SkolemLemma>& lems);
  /**
   * Do we need to lift the given lambda? This is true if the body of the
   * lambda may induce circular dependencies in model construction.
   */
  bool needsLift(const Node& lam);

  /**
   * Get the lambda for n, which is n itself if it is a lambda, or its lambda
   * representation if it is a function array constant. Returns null
   * otherwise.
   */
  static Node getLambdaFor(TNode n);
  /** Is n a lambda, or a function array constant? */
  static bool isLambda(TNode n);

  /** Beta-reduce the given lambda on the given arguments. */
  Node betaReduce(TNode lam, const std::vector<Node>& args) const;

 private:
  /**
   * Return the trust node corresponding to the lemma for the lambda
   * lifting of (lambda) term node, or null if it is not a lambda or if
   * the lambda lifting lemma has already been generated in this context.
   */
  TrustNode lift(Node node);
  /**
   * Get assertion for node, which is the axiom defining its skolem.
   */
  static Node getAssertionFor(TNode node);
  /** Get skolem for lambda term node, returns its purification skolem */
  static Node getSkolemFor(TNode node);
  /** The nodes we have already returned trust nodes for */
  NodeSet d_lifted;
  /** An eager proof generator */
  std::unique_ptr<EagerProofGenerator> d_epg;
  /** A cache for needs lift */
  std::map<Node, bool> d_needsLift;
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__LAMBDA_LIFT_H */

/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include "context/cdhashmap.h"
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
 * In the following, we say a "lambda function" is a skolem variable that
 * was introduced as a purification skolem for a lambda term.
 */
class LambdaLift : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;

 public:
  LambdaLift(Env& env);

  /**
   * process, return the trust node corresponding to the lemma for the lambda
   * lifting of (lambda) term node, or null if it is not a lambda or if
   * the lambda lifting lemma has already been generated in this context.
   */
  TrustNode lift(Node node);

  /**
   * This method has the same contract as Theory::ppRewrite.
   * Preprocess, return the trust node corresponding to the rewrite. A null
   * trust node indicates no rewrite.
   */
  TrustNode ppRewrite(Node node, std::vector<SkolemLemma>& lems);

  /** Get the lambda term for skolem, if skolem is a lambda function. */
  Node getLambdaFor(TNode skolem) const;
  /** Is skolem a lambda function? */
  bool isLambdaFunction(TNode n) const;

  /**
   * Beta-reduce node. If node is APPLY_UF and its operator is a lambda
   * function known by this class, then this method returns the beta
   * reduced version of node. We only beta-reduce the top-most application
   * in node.
   *
   * This method returns the trust node corresponding to the rewrite of node to
   * the return value. It returns the null trust node if no beta reduction is
   * possible for node.
   */
  TrustNode betaReduce(TNode node) const;
  /** Beta-reduce the given lambda on the given arguments. */
  Node betaReduce(TNode lam, const std::vector<Node>& args) const;

 private:
  /**
   * Get assertion for node, which is the axiom defining
   */
  static Node getAssertionFor(TNode node);
  /** Get skolem for lambda term node, returns its purification skolem */
  static Node getSkolemFor(TNode node);
  /** The nodes we have already returned trust nodes for */
  NodeSet d_lifted;
  /** Mapping skolems to their lambda */
  NodeNodeMap d_lambdaMap;
  /** An eager proof generator */
  std::unique_ptr<EagerProofGenerator> d_epg;
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__LAMBDA_LIFT_H */

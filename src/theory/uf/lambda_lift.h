/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace uf {

/**
 */
class LambdaLift : protected EnvObj
{
  typedef context::CDHashSet<Node> NodeSet;
  typedef context::CDHashMap<Node, Node> NodeNodeMap;

 public:
  LambdaLift(Env& env);

  /** process, return the trust node corresponding to the lemma */
  TrustNode lift(Node node);

  /** process, return the trust node corresponding to the rewrite */
  TrustNode ppRewrite(Node node, std::vector<SkolemLemma>& lems);

  /** needs lifting */
  bool needsLift(TNode skolem) const;

  /** Get lambda for skolem */
  Node getLambdaFor(TNode skolem) const;

  /** Beta-reduce */
  TrustNode betaReduce(TNode node) const;
  /** Beta-reduce */
  Node betaReduce(TNode lam, const std::vector<Node>& args) const;

 private:
  /** Get assertion for */
  static Node getAssertionFor(TNode node);
  /** Get skolem for */
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
}  // namespace cvc5

#endif /* CVC5__THEORY__UF__LAMBDA_LIFT_H */

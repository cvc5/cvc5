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

#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace uf {

/**
 * Module for doing various operations on lambdas.
 *
 * Lambdas are not replaced by skolems during preprocessing. Instead, they
 * occur directly in constraints, and are beta-reduced on demand by the
 * higher-order extension when they are equated to ordinary functions.
 */
class LambdaLift : protected EnvObj
{
 public:
  LambdaLift(Env& env);

  /**
   * Do we need to lift the given lambda? This is true if the body of the
   * lambda may induce circular dependencies in model construction.
   */
  bool needsLift(const Node& lam);
  /**
   * Get the lemma for lifting n, which is a lambda or function array constant
   * that is equal to the ordinary function f. This lemma is:
   *   (=> (= f n) (forall x. (= (f x) (lam x))))
   * where lam is the lambda for n.
   */
  Node getLiftLemma(const Node& f, const Node& n) const;

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
  /** A cache for needs lift */
  std::map<Node, bool> d_needsLift;
};

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__LAMBDA_LIFT_H */

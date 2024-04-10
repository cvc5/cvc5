/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper on linear solver
 */

#pragma once

#include "context/cdhashmap.h"
#include "smt/env_obj.h"
#include "theory/arith/linear/theory_arith_private.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {

class TheoryModel;

namespace arith {

class BranchAndBound;

namespace linear {

/**
 * A wrapper of the linear arithmetic solver.
 */
class LinearSolver : protected EnvObj
{
 public:
  LinearSolver(Env& env,
               TheoryState& ts,
               InferenceManager& im,
               BranchAndBound& bab);
  /** finish initialize */
  void finishInit(eq::EqualityEngine* ee);
  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n);
  /** Propagate at the given effort level */
  void propagate(Theory::Effort e);
  /** Explain propagated literal n */
  TrustNode explain(TNode n);
  /**
   * Collect model values. This is the main method for extracting information
   * about how to construct the model. This method relies on the caller for
   * processing the map, which is done so that other modules (e.g. the
   * non-linear extension) can modify arithModel before it is sent to the model.
   *
   * @param termSet The set of relevant terms
   * @param arithModel Mapping from terms (of int/real type) to their values.
   * The caller should assert equalities to the model for each entry in this
   * map.
   * @param arithModelIllTyped Mapping from terms (of int type) to real values.
   * This is used for catching cases where this solver mistakenly set an
   * integer variable to a real.
   */
  void collectModelValues(const std::set<Node>& termSet,
                          std::map<Node, Node>& arithModel,
                          std::map<Node, Node>& arithModelIllTyped);
  /** Presolve */
  void presolve();
  /** Notify restart */
  void notifyRestart();
  /** Preprocess assert */
  Theory::PPAssertStatus ppAssert(TrustNode tin,
                                  TrustSubstitutionMap& outSubstitutions);
  /** Preprocess static learn */
  void ppStaticLearn(TNode in, NodeBuilder& learned);

  EqualityStatus getEqualityStatus(TNode a, TNode b);

  /** Called when n is notified as being a shared term with TheoryArith. */
  void notifySharedTerm(TNode n);
  /** Get candidate model value */
  Node getCandidateModelValue(TNode var);
  /** Do entailment check */
  std::pair<bool, Node> entailmentCheck(TNode lit);
  //--------------------------------- standard check
  /** Pre-check, called before the fact queue of the theory is processed. */
  bool preCheck(Theory::Effort level, bool newFacts);
  /** Pre-notify fact. */
  void preNotifyFact(TNode fact);
  /**
   * Post-check, called after the fact queue of the theory is processed. Returns
   * true if a conflict or lemma was emitted.
   */
  bool postCheck(Theory::Effort level);
  //--------------------------------- end standard check
  /**
   * Found non-linear? This returns true if this solver ever encountered
   * any non-linear terms that were unhandled. Note that this class is not
   * responsible for handling non-linear arithmetic. If the owner of this
   * class does not handle non-linear arithmetic in another way, then
   * setModelUnsound should be called on the output channel of TheoryArith.
   */
  bool foundNonlinear() const;

  /** get the congruence manager, if we are using one */
  ArithCongruenceManager* getCongruenceManager();

  //======================
  bool outputTrustedLemma(TrustNode lemma, InferenceId id);
  void outputTrustedConflict(TrustNode conf, InferenceId id);
  void outputPropagate(TNode lit);
  void spendResource(Resource r);

 private:
  /** The inference manager */
  InferenceManager& d_im;
  /** The solver */
  TheoryArithPrivate d_internal;
};

}  // namespace linear
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

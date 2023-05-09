/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Dejan Jovanovic, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Base class for shared solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__SHARED_SOLVER__H
#define CVC5__THEORY__SHARED_SOLVER__H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"

namespace cvc5::internal {

class LogicInfo;
class ProofNodeManager;
class TheoryEngine;

namespace theory {

struct EeSetupInfo;
class TheoryInferenceManager;

/**
 * A base class for shared solver. The shared solver is the component of theory
 * engine that behaves like a theory solver, and whose purpose is to ensure the
 * main theory combination method can be performed in CombinationEngine.
 * Its role is to:
 * (1) Notify the individual theories of shared terms via addSharedTerms,
 * (2) Be the official interface for equality statuses,
 * (3) Propagate equalities to TheoryEngine when necessary and explain them.
 */
class SharedSolver : protected EnvObj
{
 public:
  SharedSolver(Env& env, TheoryEngine& te);
  virtual ~SharedSolver() {}
  //------------------------------------- initialization
  /**
   * Returns true if we need an equality engine, this has the same contract
   * as Theory::needsEqualityEngine.
   */
  virtual bool needsEqualityEngine(theory::EeSetupInfo& esi);
  /**
   * Set the equality engine. This should be called by equality engine manager
   * during EqEngineManager::initializeTheories.
   */
  virtual void setEqualityEngine(eq::EqualityEngine* ee) = 0;
  //------------------------------------- end initialization
  /**
   * Called when the given atom is pre-registered in TheoryEngine.
   *
   * This calls Theory::preRegisterTerm on all subterms of atom for the
   * appropriate theories.
   *
   * Also, if sharing is enabled, this adds atom as an equality to propagate in
   * the shared terms database if it is an equality, and adds its shared terms
   * to the appropariate theories.
   *
   * @param atom The atom to preregister
   */
  void preRegister(TNode atom);
  /**
   * Pre-notify assertion fact with the given atom. This is called when any
   * fact is asserted in TheoryEngine, just before it is dispatched to the
   * appropriate theory.
   *
   * This calls Theory::notifySharedTerm for the shared terms of the atom.
   */
  void preNotifySharedFact(TNode atom);
  /**
   * Get the equality status of a and b.
   *
   * This method is used by theories via Valuation mostly for determining their
   * care graph.
   */
  virtual EqualityStatus getEqualityStatus(TNode a, TNode b);
  /**
   * Explain literal, which returns a conjunction of literals that entail
   * the given one.
   */
  virtual TrustNode explain(TNode literal, TheoryId id) = 0;
  /**
   * Assert n to the shared terms database.
   *
   * This method is called by TheoryEngine when a fact has been marked to
   * send to THEORY_BUILTIN, meaning that shared terms database should
   * maintain this fact. In the distributed equality engine architecture,
   * this is the case when either an equality is asserted from the SAT solver
   * or a theory propagates an equality between shared terms.
   */
  virtual void assertShared(TNode n, bool polarity, TNode reason) = 0;
  /** Is term t a shared term? */
  virtual bool isShared(TNode t) const;

  /**
   * Propagate the predicate with polarity value on the output channel of this
   * solver.
   */
  bool propagateLit(TNode predicate, bool value);
  /**
   * Method called by equalityEngine when a becomes (dis-)equal to b and a and b
   * are shared with the theory. Returns false if there is a direct conflict
   * (via rewrite for example).
   */
  bool propagateSharedEquality(theory::TheoryId theory,
                               TNode a,
                               TNode b,
                               bool value);
  /** Send lemma to the theory engine, atomsTo is the theory to send atoms to */
  void sendLemma(TrustNode trn, TheoryId atomsTo, InferenceId id);
  /** Send conflict to the theory engine */
  void sendConflict(TrustNode trn, InferenceId id);

 protected:
  /** Solver-specific pre-register shared */
  virtual void preRegisterSharedInternal(TNode t) = 0;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** The database of shared terms.*/
  SharedTermsDatabase d_sharedTerms;
  /** Default visitor for pre-registration */
  PreRegisterVisitor d_preRegistrationVisitor;
  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;
  /** Theory inference manager of theory builtin */
  TheoryInferenceManager* d_im;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__SHARED_SOLVER__H */

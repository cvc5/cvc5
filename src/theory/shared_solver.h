/*********************                                                        */
/*! \file shared_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Base class for shared solver
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SHARED_SOLVER__H
#define CVC4__THEORY__SHARED_SOLVER__H

#include "expr/node.h"
#include "theory/ee_setup_info.h"
#include "theory/logic_info.h"
#include "theory/shared_terms_database.h"
#include "theory/term_registration_visitor.h"
#include "theory/valuation.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * A base class for shared solver. The shared solver is the component of theory
 * engine that behaves like a theory solver, and whose purpose is to ensure the
 * main theory combination method can be performed in CombinationEngine.
 * Its role is to:
 * (1) Notify the individual theories of shared terms via addSharedTerms,
 * (2) Be the official interface for equality statuses,
 * (3) Propagate equalities to TheoryEngine when necessary and explain them.
 */
class SharedSolver
{
 public:
  SharedSolver(TheoryEngine& te);
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
   * Called when the given term t is pre-registered in TheoryEngine.
   *
   * This adds t as an equality to propagate in the shared terms database
   * if it is an equality, or adds its shared terms if it involves multiple
   * theories.
   *
   * @param t The term to preregister
   * @param multipleTheories Whether multiple theories are present in t.
   */
  void preRegisterShared(TNode t, bool multipleTheories);
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
   * Assert equality to the shared terms database.
   *
   * This method is called by TheoryEngine when a fact has been marked to
   * send to THEORY_BUILTIN, meaning that shared terms database should
   * maintain this fact. This is the case when either an equality is
   * asserted from the SAT solver or a theory propagates an equality between
   * shared terms.
   */
  virtual void assertSharedEquality(TNode equality,
                                    bool polarity,
                                    TNode reason) = 0;
  /** Is term t a shared term? */
  virtual bool isShared(TNode t) const;

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
  void sendLemma(TrustNode trn, TheoryId atomsTo);

 protected:
  /** Solver-specific pre-register shared */
  virtual void preRegisterSharedInternal(TNode t) = 0;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** The database of shared terms.*/
  SharedTermsDatabase d_sharedTerms;
  /** Visitor for collecting shared terms */
  SharedTermsVisitor d_sharedTermsVisitor;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__SHARED_SOLVER__H */

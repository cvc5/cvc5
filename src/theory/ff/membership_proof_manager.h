/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Ideal membership proofs.
 */

#include "cvc5_private.h"

#ifdef CVC5_USE_COCOA

#ifndef CVC5__THEORY__FF__MEMBERSHIP_PROOF_MANAGER_H
#define CVC5__THEORY__FF__MEMBERSHIP_PROOF_MANAGER_H

// external includes
#include <CoCoA/DistrMPolyInlFpPP.H>
#include <CoCoA/DistrMPolyInlPP.H>
#include <CoCoA/ideal.H>
#include <CoCoA/ring.H>

// std includes
#include <functional>
#include <unordered_map>
#include <vector>

// internal includes
#include "expr/node.h"
#include "proof/proof.h"
#include "smt/env_obj.h"
#include "theory/ff/cocoa_encoder.h"
#include "theory/ff/proof_utils.h"

namespace cvc5::internal {
namespace theory {
namespace ff {

/**
 * Tracks the computations done by CoCoALib to justify ideal membership.
 *
 * CoCoALib calls the hooks of this class while computing a Groebner basis or
 * while reducing a polynomial modulo one. We first collect all the information
 * needed for proof construction and build the proof later, since we may end up
 * using only a subset of the input (an unsat core restriction).
 */
class MembershipProofManager : protected EnvObj
{
 public:
  MembershipProofManager(Env& env,
                         const std::vector<Node>& polys,
                         Node ideal,
                         CoCoA::ring ring,
                         CocoaEncoder& enc,
                         CDProof* proof);

  /**
   * Install our hooks into CoCoALib. They are then called by CoCoALib during
   * reduction and computation of S-polynomials. Don't move the object after
   * calling this. Must be called before CoCoA is used.
   */
  void setFunctionPointers();

  /**
   * Unhook from CoCoA callbacks. Should be called after you're done producing
   * proofs. Also clears the global proof `std::function`s so they don't retain
   * captured pointers into this manager past its lifetime.
   */
  void unsetFunctionPointers();

  /**
   * Destructor. If `setFunctionPointers()` was called and
   * `unsetFunctionPointers()` has not yet run (e.g. stack unwinding through a
   * `FfTimeoutException`), the global CoCoA proof slots still hold
   * `std::function`s that captured `this`. Detach them here so a later CoCoA
   * call doesn't dereference freed memory.
   */
  ~MembershipProofManager();
  /**
   * Get the membership fact for a polynomial.
   * @param poly a polynomial that is already registered in this manager.
   */
  Node getMembershipFact(CoCoA::ConstRefRingElem poly);
  /**
   * Get the membership fact for an arbitrary element of the ideal, producing
   * its proof if we do not have one yet.
   * @param poly the polynomial to prove membership of; *must* be an element of
   * the ideal.
   * @param ideal the CoCoALib representation of the ideal.
   */
  Node proveIdealMembership(CoCoA::RingElem poly, CoCoA::ideal ideal);
  /**
   * Restrict ourselves to a subset of the original generators. Used for unsat
   * core restriction.
   */
  void updateIdeal(Node ideal);
  /** Add the collected proof steps to the proof. */
  void registerProofs();

 private:
  /** Build the term stating that poly is in the current ideal. */
  Node produceMembershipNode(Node poly);
  /** Store the information needed to later add a step for poly. */
  void storeProof(Node poly,
                  ProofRule id,
                  std::vector<Node> children,
                  std::vector<Node> args);

  /** Called when s = spoly(p, q). */
  void sPoly(CoCoA::ConstRefRingElem p,
             CoCoA::ConstRefRingElem q,
             CoCoA::ConstRefRingElem s);
  /** Called when we start reducing p. */
  void reductionStart(CoCoA::ConstRefRingElem p);
  /** Called when there is a reduction by q. */
  void reductionStep(CoCoA::ConstRefRingElem q);
  /** Called when we finish reducing, with result r. */
  void reductionEnd(CoCoA::ConstRefRingElem r);
  /** Called to capture the multiplier used in a reduction. */
  void storeMultiplier(CoCoA::ConstRefRingElem mul);
  /** As above, for a multiplier that CoCoALib has not wrapped in a RingElem. */
  template <typename T>
  void storeMultiplierRaw(T& mul);
  /** Called when monic is the result of making poly monic. */
  void monicProof(CoCoA::ConstRefRingElem poly, CoCoA::ConstRefRingElem monic);
  /** Called at the start of a membership test of p. */
  void membershipStart(CoCoA::ConstRefRingElem p);
  /** Called for each reduction step of a membership test. */
  void membershipStep(CoCoA::RingElem s);
  /** Called at the end of a membership test. */
  void membershipEnd();

  /** the polynomials used for reduction during Groebner basis computation */
  std::vector<CoCoA::RingElem> d_reductionSeq{};
  /** the multipliers of the polynomials in d_reductionSeq */
  std::vector<CoCoA::RingElem> d_multiplierSeq{};
  /** the polynomials used for reduction during a membership test */
  std::vector<CoCoA::RingElem> d_membershipSeq{};

  /**
   * Our hooks, stored so that CoCoALib holds pointers that stay valid.
   *
   * Groebner basis proof production uses d_sPoly, d_reductionStart,
   * d_reductionStep and d_reductionEnd; membership proof production uses
   * d_membershipStart, d_membershipStep and d_membershipEnd; both use
   * d_storeMultiplier.
   */
  std::function<void(CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem,
                     CoCoA::ConstRefRingElem)>
      d_sPoly{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionStep{};
  std::function<void(CoCoA::ConstRefRingElem)> d_reductionEnd{};
  std::function<void(CoCoA::ConstRefRingElem, CoCoA::ConstRefRingElem)>
      d_monicProof{};
  std::function<void(CoCoA::ConstRefRingElem)> d_membershipStart{};
  std::function<void(CoCoA::ConstRefRingElem)> d_membershipStep{};
  std::function<void(void)> d_membershipEnd{};
  std::function<void(CoCoA::ConstRefRingElem)> d_storeMultiplier{};
  std::function<void(CoCoA::DistrMPolyInlPP&)> d_storeMultiplierRaw{};
  std::function<void(CoCoA::DistrMPolyInlFpPP&)> d_storeMultiplierRawFp{};

  /**
   * The ideal that we are currently proving membership facts for: a term whose
   * children are the generators.
   */
  Node d_ideal;
  /** the ring of polynomials that our ideal lives in */
  CoCoA::ring d_cocoaRing;
  /** map: polynomial to the proof step that justifies its membership */
  std::unordered_map<Node, ProofInfo> d_factToProof;
  /** the encoder built in sub_theory; used for decoding */
  CocoaEncoder& d_enc;
  /** the polynomial whose membership we are currently testing */
  CoCoA::RingElem d_reducingPoly;
  /** the proof that we add our steps to */
  CDProof* d_proof;

  /** True between `setFunctionPointers()` and `unsetFunctionPointers()`. */
  bool d_handlersRegistered{false};
};

}  // namespace ff
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FF__MEMBERSHIP_PROOF_MANAGER_H */

#endif /* CVC5_USE_COCOA */

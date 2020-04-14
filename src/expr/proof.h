/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Proof utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_H
#define CVC4__EXPR__PROOF_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_node.h"

namespace CVC4 {

/**
 * A (context-dependent) proof.
 *
 * This maintains a context-dependent map from formulas to ProofNode shared
 * pointers. When a proof step is registered, it uses pointers to ProofNode
 * objects to link ProofNode objects together. These pointers can in turn be
 * modified as further steps are registered.
 *
 * Based on this class, we can ask for the proof of a given fact, which returns
 * a ProofNode object that has linked together the proof steps registered to
 * this object.
 *
 * As an example, if we call:
 * - registerStep( A, ID_A, { B, C }, {}, false )
 * - registerStep( B, ID_B, { D }, {}, false )
 * Then getProof( A ) returns the proof of the form:
 *   ID_A( ID_B( ASSUME( D ) ), ASSUME( C ) )
 * Notice that the above calls to registerStep can be made in either order.
 *
 * The method registerProof makes multiple calls to registerStep. Continuing
 * the above example, if we call:
 * - registerProof( E, ID_E( ASSUME( A ), ASSUME( B ) )
 * for instance will result in getProof( E ) returning:
 *   ID_E( ID_A( PB, ASSUME( C ) ), PB ), where PB is ID_B( ASSUME( D ) ).
 * The calls to registerProof and registerStep above can be made in any order.
 *
 * This class overwrites assumptions wherever possible, and maintains a policy
 * on when the other proof steps are overwritten. Currently, no other
 * proof step is overwritten when provided a second time. This is the case
 * for registerProof calls as well.
 * As an example, say that we have these calls:
 * - registerStep( B, ID_B1 {}, {}, false )
 * - registerStep( A, ID_A1, { B, C }, {}, false )
 * At this point, getProof( A ) returns:
 *   ID_A1( ID_B1(), ASSUME(C) )
 * Now, assume an additional call is made to:
 * - registerProof( D, ID_D( ID_A2( ID_B2(), ID_C() ) ) )
 * where ID_B2() and ID_C() prove B and C respectively. Then, getProof( D )
 * returns:
 *   ID_D( ID_A1( ID_B1(), ID_C() ) )
 * Notice that the steps with ID_A1 and ID_B1 were not overwritten by this call,
 * whereas the assumption of C was overwritten by the proof ID_C(). Notice that
 * the proof of D was completely traversed, despite encountering formulas, A and
 * B, that were already given proof steps.
 *
 * Notice the map from Nodes to ProofNodes is context-dependent and is
 * backtracked when the context backtracks.
 */
class CDProof
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofNodeMap;

 public:
  CDProof(context::Context* c, ProofNodeManager* pnm);
  ~CDProof() {}
  /** Get proof for fact, or nullptr if it does not exist */
  std::shared_ptr<ProofNode> getProof(Node fact) const;
  /** Register step
   *
   * @param expected The intended conclusion of this proof step.
   * @param id The identifier for the proof step.
   * @param children The antecendant of the proof step. Each children[i] should
   * be a fact previously registered as a conclusion of a registerStep call
   * when ensureChildren is true.
   * @param args The arguments of the proof step.
   *
   * This returns expected if indeed the proof step proves expected. This can
   * fail if the proof has a different (or invalid) conclusion, or if one of the
   * children does not have a proof and ensureChildren is true.
   *
   * This method does not overwrite proofs for facts that are already proven
   * and are not assumptions. However, it will overwrite the proof for fact if
   * it was previously proved by assumption.
   *
   * Additionally, it will create proofs by assumption of the facts in
   * children when ensureChildren is false.
   *
   * Notice that ensureChildren should be true if the proof is being
   * constructed is a strictly eager fashion; ensureChildren should be false
   * if the steps are registered lazily or out of order.
   */
  Node registerStep(Node expected,
                    ProofStep id,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    bool ensureChildren = false);
  /** Register proof
   *
   * @param fact The intended conclusion of the proof.
   * @param pn The proof of the given fact.
   *
   * This method returns fact if pn is a proof of fact, and null otherwise.
   * If it returns fact, it registers a copy of all of the subnodes of pn to
   * this proof class.
   *
   * This method is implemented by calling registerStep above for the
   * appropriate subnodes of pn. Thus this method does *not* overwrite proofs
   * for facts that are already proven are not assumptions. Also notice that
   * no points in pn are taken by this call; instead relevant portions are
   * deep copied (via calls to registerStep).
   */
  Node registerProof(Node fact, std::shared_ptr<ProofNode> pn);

 protected:
  /** The proof manager, used for allocating new ProofNode objects */
  ProofNodeManager* d_manager;
  /** The nodes of the proof */
  NodeProofNodeMap d_nodes;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_MANAGER_H */

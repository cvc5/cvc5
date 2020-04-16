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
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"

namespace CVC4 {

/**
 * A (context-dependent) proof.
 *
 * This maintains a context-dependent map from formulas to ProofNode shared
 * pointers. When a step is registered, it internally uses ProofNode
 * pointers to link the steps in the proof together.
 *
 * It is important to note that the premises of proof steps given to this class
 * are *Node* not *ProofNode*. In other words, the user of this class does
 * not have to manage ProofNode pointers while using this class. Instead,
 * ProofNode is the final product of this class, via the getProof interface,
 * which returns a ProofNode object that has linked together the proof steps
 * registered to this object.
 *
 * As an example, let A, B, C, D be formulas represented by Node objects. If we
 * call:
 * - registerStep( A, ID_A, { B, C }, {} )
 * - registerStep( B, ID_B, { D }, {} )
 * Then getProof( A ) returns the ProofNode of the form:
 *   ID_A( ID_B( ASSUME( D ) ), ASSUME( C ) )
 * Notice that the above calls to registerStep can be made in either order.
 *
 * If the user wants to combine proofs, then a registerProof interface is
 * available. The method registerProof can be seen as syntax sugar for making
 * multiple calls to registerStep. Continuing the above example, if we call:
 * - registerProof( E, ID_E( ASSUME( A ), ASSUME( B ) )
 * is the same as calling steps corresponding the steps in the provided proof
 * bottom-up, starting from the leaves:
 * --- registerStep( A, ASSUME, {}, {}, true )
 * --- registerStep( B, ASSUME, {}, {}, true )
 * --- registerStep( E, ID_E, { A, B }, {}, true )
 * This will result in getProof( E ) returning:
 *   ID_E( ID_A( PB, ASSUME( C ) ), PB )
 * where PB is ID_B( ASSUME( D ) ). Notice that the proof of A by ID_A was not
 * overwritten by ASSUME.
 *
 * When forceOverwrite is false, the method registerStep overwrites assumptions
 * wherever possible, and does not modify any other ProofNode objects (apart
 * from those whose rule is ASSUME).
 *
 * As another example, say that we call:
 * - registerStep( B, ID_B1 {}, {} )
 * - registerStep( A, ID_A1, {B, C}, {} )
 * At this point, getProof( A ) returns:
 *   ID_A1( ID_B1(), ASSUME(C) )
 * Now, assume an additional call is made to:
 * - registerProof( D, ID_D( ID_A2( ID_B2(), ID_C() ) ) )
 * where assume ID_B2() and ID_C() prove B and C respectively. This call is
 * equivalent to calling:
 * --- registerStep( B, ID_B2, {}, {}, true )
 * --- registerStep( C, ID_C, {}, {}, true )
 * --- registerStep( A, ID_A2, {B, C}, {}, true )
 * --- registerStep( D, ID_D, {A}, {}, true )
 * Afterwards, getProof( D ) returns:
 *   ID_D( ID_A1( ID_B1(), ID_C() ) )
 * Notice that the steps with ID_A1 and ID_B1 were not overwritten by this call,
 * whereas the assumption of C was overwritten by the proof ID_C(). Notice that
 * the proof of D was completely traversed, despite encountering formulas, A and
 * B, that were already given proof steps.
 *
 * This class requires a ProofNodeManager object, which is a trusted way of
 * allocating ProofNode pointers. This manager may have an underlying checker,
 * although this is not required. It also (optionally) takes a context c.
 * If no context is provided, then this proof is context-independent. This
 * is implemented internally by using a dummy context that is never pushed
 * or popped. The map from Nodes to ProofNodes is context-dependent and is
 * backtracked when its context backtracks.
 */
class CDProof
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofNodeMap;

 public:
  CDProof(ProofNodeManager* pnm, context::Context* c = nullptr);
  ~CDProof();
  /**
   * Get proof for fact, or nullptr if it does not exist. Notice that this call
   * does *not* clone the ProofNode object. Hence, the returned proof may
   * be updated by further calls to this class. The caller should call
   * ProofNode::clone if they want to own it.
   */
  std::shared_ptr<ProofNode> getProof(Node fact) const;
  /** Register step
   *
   * @param expected The intended conclusion of this proof step. This must be
   * non-null.
   * @param id The identifier for the proof step.
   * @param children The antecendant of the proof step. Each children[i] should
   * be a fact previously registered as a conclusion of a registerStep call
   * when ensureChildren is true.
   * @param args The arguments of the proof step.
   * @param ensureChildren Whether we wish to ensure steps have been registered
   * for all nodes in children
   * @param forceOverwrite Whether we wish to overwrite if a step for expected
   * was already provided (via a previous call to registerStep)
   * @return The argument expected if indeed the proof step proves expected, or
   * null otherwise. The latter can happen if the proof has a different (or
   * invalid) conclusion, or if one of the children does not have a proof and
   * ensureChildren is true.
   *
   * This method only overwrite proofs for facts that were registered as
   * steps with id ASSUME.
   *
   * Additionally, it will create proofs justified by ASSUME of the facts in
   * children that have not already been proven when ensureChildren is false.
   *
   * Notice that ensureChildren should be true if the proof is being
   * constructed is a strictly eager fashion (bottom up from its leaves), while
   * ensureChildren should be false if the steps are registered lazily or out
   * of order.
   */
  Node registerStep(Node expected,
                    PfRule id,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    bool ensureChildren = false,
                    bool forceOverwrite = false);
  /** Register proof
   *
   * @param fact The intended conclusion of the proof.
   * @param pn The proof of the given fact.
   * @param forceOverwrite Whether we wish to force overwriting if a step was
   * already provided, for each node in the proof.
   * @return fact if pn is a proof of fact, and null otherwise. If it returns
   * fact, it registers a copy of all of the subnodes of pn to this proof class.
   *
   * This method is implemented by calling registerStep above for the
   * appropriate subnodes of pn. This means that new ProofNode objects may be
   * generated by this call, and further modifications to pn does not impact
   * the data members of this class.
   */
  Node registerProof(Node fact,
                     std::shared_ptr<ProofNode> pn,
                     bool forceOverwrite = false);

 protected:
  /** The proof manager, used for allocating new ProofNode objects */
  ProofNodeManager* d_manager;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** The nodes of the proof */
  NodeProofNodeMap d_nodes;
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_MANAGER_H */

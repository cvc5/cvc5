/*********************                                                        */
/*! \file proof.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
#include "expr/proof_generator.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_step_buffer.h"

namespace CVC4 {

/**
 * A (context-dependent) proof.
 *
 * This maintains a context-dependent map from formulas to ProofNode shared
 * pointers. When a step is added, it internally uses mutable ProofNode pointers
 * to link the steps in the proof together.
 *
 * It is important to note that the premises of proof steps given to this class
 * are *Node* not *ProofNode*. In other words, the user of this class does
 * not have to manage ProofNode pointers while using this class. Instead,
 * ProofNode is the final product of this class, via the getProof interface,
 * which returns a ProofNode object that has linked together the proof steps
 * added to this object.
 *
 * Its main interface is the function addStep, which registers a single
 * step in the proof. Its interface is:
 *   addStep( <conclusion>, <rule>, <premises>, <args>, ...<options>... )
 * where conclusion is what to be proven, rule is an identifier, premises
 * are the formulas that imply conclusion, and args are additional arguments to
 * the proof rule application. The options include whether we ensure children
 * proofs already exist for the premises and our policty for overwriting
 * existing steps.
 *
 * As an example, let A, B, C, D be formulas represented by Nodes. If we
 * call:
 * - addStep( A, ID_A, { B, C }, {} )
 * - addStep( B, ID_B, { D }, {} )
 * - addStep( E, ID_E, {}, {} )
 * with default options, then getProof( A ) returns the ProofNode of the form:
 *   ID_A( ID_B( ASSUME( D ) ), ASSUME( C ) )
 * Notice that the above calls to addStep can be made in either order. The
 * proof step for E was not involved in the proof of A.
 *
 * If the user wants to combine proofs, then a addProof interface is
 * available. The method addProof can be seen as syntax sugar for making
 * multiple calls to addStep. Continuing the above example, if we call:
 * - addProof( F, ID_F( ASSUME( A ), ASSUME( E ) ) )
 * is the same as calling steps corresponding the steps in the provided proof
 * bottom-up, starting from the leaves.
 * --- addStep( A, ASSUME, {}, {}, true )
 * --- addStep( E, ASSUME, {}, {}, true )
 * --- addStep( F, ID_F, { A, E }, {}, true )
 * The fifth argument provided indicates that we want to ensure child proofs
 * are already available for the step (see ensureChildren in addStep below).
 * This will result in getProof( F ) returning:
 *   ID_F( ID_A( ID_B( ASSUME( D ) ), ASSUME( C ) ), ID_E() )
 * Notice that the proof of A by ID_A was not overwritten by ASSUME in the
 * addStep call above.
 *
 * The default policy for overwriting proof steps (CDPOverwrite::ASSUME_ONLY)
 * gives ASSUME a special status. An ASSUME step can be seen as a step whose
 * justification has not yet been provided. Thus, it is always overwritten.
 * Other proof rules are never overwritten, unless the argument opolicy is
 * CDPOverwrite::ALWAYS.
 *
 * As an another example, say that we call:
 * - addStep( B, ID_B1 {}, {} )
 * - addStep( A, ID_A1, {B, C}, {} )
 * At this point, getProof( A ) returns:
 *   ID_A1( ID_B1(), ASSUME(C) )
 * Now, assume an additional call is made to addProof, where notice
 * the overwrite policy is CDPOverwrite::ASSUME_ONLY by default:
 * - addProof( D, ID_D( ID_A2( ID_B2(), ID_C() ) ) )
 * where assume ID_B2() and ID_C() prove B and C respectively. This call is
 * equivalent to calling:
 * --- addStep( B, ID_B2, {}, {}, true )
 * --- addStep( C, ID_C, {}, {}, true )
 * --- addStep( A, ID_A2, {B, C}, {}, true )
 * --- addStep( D, ID_D, {A}, {}, true )
 * Afterwards, getProof( D ) returns:
 *   ID_D( ID_A1( ID_B1(), ID_C() ) )
 * Notice that the steps with ID_A1 and ID_B1 were not overwritten by this call,
 * whereas the assumption of C was overwritten by the proof ID_C(). Notice that
 * the proof of D was completely traversed in addProof, despite encountering
 * formulas, A and B, that were already given proof steps.
 *
 * This class requires a ProofNodeManager object, which is a trusted way of
 * allocating ProofNode pointers. This manager may have an underlying checker,
 * although this is not required. It also (optionally) takes a context c.
 * If no context is provided, then this proof is context-independent. This
 * is implemented internally by using a dummy context that is never pushed
 * or popped. The map from Nodes to ProofNodes is context-dependent and is
 * backtracked when its context backtracks.
 *
 * An important invariant of this object is that there exists (at most) one
 * proof step for each Node. Thus, the ProofNode objects returned by this
 * class share proofs for common subformulas, as guaranteed by the fact that
 * Node objects have perfect sharing.
 *
 * Notice that this class is agnostic to symmetry of equality. In other
 * words, adding a step that concludes (= x y) is effectively the same as
 * providing a step that concludes (= y x) from the point of view of a user
 * of this class. This is accomplished by adding SYMM steps on demand when
 * a formula is looked up. For example say we call:
 * - addStep( (= x y), ID_1 {}, {} )
 * - addStep( P, ID_2, {(= y x)}, {} )
 * Afterwards, getProof( P ) returns:
 *   ID_2( SYMM( ID_1() ) )
 * where notice SYMM was added so that (= y x) is a premise of the application
 * of ID_2. More generally, CDProof::isSame(F,G) returns true if F and G are
 * essentially the same formula according to this class.
 */
class CDProof : public ProofGenerator
{
 public:
  CDProof(ProofNodeManager* pnm, context::Context* c = nullptr);
  virtual ~CDProof();
  /**
   * Make proof for fact.
   *
   * This method always returns a non-null ProofNode. It may generate new
   * steps so that a ProofNode can be constructed for fact. In particular,
   * if no step exists for fact, then we may construct and return ASSUME(fact).
   * If fact is of the form (= t s), no step exists for fact, but a proof
   * P for (= s t) exists, then this method returns SYMM(P).
   *
   * Notice that this call does *not* clone the ProofNode object. Hence, the
   * returned proof may be updated by further calls to this class. The caller
   * should call ProofNode::clone if they want to own it.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** Add step
   *
   * @param expected The intended conclusion of this proof step. This must be
   * non-null.
   * @param id The identifier for the proof step.
   * @param children The antecendants of the proof step. Each children[i] should
   * be a fact previously added as a conclusion of an addStep call when
   * ensureChildren is true.
   * @param args The arguments of the proof step.
   * @param ensureChildren Whether we wish to ensure steps have been added
   * for all nodes in children
   * @param opolicy Policy for whether to overwrite if a step for
   * expected was already provided (via a previous call to addStep)
   * @return The true if indeed the proof step proves expected, or
   * false otherwise. The latter can happen if the proof has a different (or
   * invalid) conclusion, or if one of the children does not have a proof and
   * ensureChildren is true.
   *
   * This method may create proofs justified by ASSUME of the facts in
   * children that have not already been proven when ensureChildren is false.
   * Notice that ensureChildren should be true if the proof is being
   * constructed is a strictly eager fashion (bottom up from its leaves), while
   * ensureChildren should be false if the steps are added lazily or out
   * of order.
   *
   * This method only overwrites proofs for facts that were added as
   * steps with id ASSUME when opolicy is CDPOverwrite::ASSUME_ONLY, and always
   * (resp. never) overwrites an existing step if one was provided when opolicy
   * is CDPOverwrite::ALWAYS (resp. CDPOverwrite::NEVER).
   */
  bool addStep(Node expected,
               PfRule id,
               const std::vector<Node>& children,
               const std::vector<Node>& args,
               bool ensureChildren = false,
               CDPOverwrite opolicy = CDPOverwrite::ASSUME_ONLY);
  /** Version with ProofStep */
  bool addStep(Node expected,
               const ProofStep& step,
               bool ensureChildren = false,
               CDPOverwrite opolicy = CDPOverwrite::ASSUME_ONLY);
  /** Version with ProofStepBuffer */
  bool addSteps(const ProofStepBuffer& psb,
                bool ensureChildren = false,
                CDPOverwrite opolicy = CDPOverwrite::ASSUME_ONLY);
  /** Add proof
   *
   * @param pn The proof of the given fact.
   * @param opolicy Policy for whether to force overwriting if a step
   * was already provided. This is used for each node in the proof if doCopy
   * is true.
   * @param doCopy Whether we make a deep copy of the pn.
   * @return true if all steps were successfully added to this class. If it
   * returns true, it registers a copy of all of the subnodes of pn to this
   * proof class.
   *
   * If doCopy is true, this method is implemented by calling addStep above for
   * all subnodes of pn, traversed as a dag. This means that fresh ProofNode
   * objects may be generated by this call, and further modifications to pn do
   * not impact the internal data of this class.
   */
  bool addProof(std::shared_ptr<ProofNode> pn,
                CDPOverwrite opolicy = CDPOverwrite::ASSUME_ONLY,
                bool doCopy = false);
  /** Return true if fact already has a proof step */
  bool hasStep(Node fact);
  /** Get the proof manager for this proof */
  ProofNodeManager* getManager() const;
  /**
   * Is same? Returns true if f and g are the same formula, or if they are
   * symmetric equalities. If two nodes f and g are the same, then a proof for
   * f suffices as a proof for g according to this class.
   */
  static bool isSame(TNode f, TNode g);
  /**
   * Get symmetric fact (a g such that isSame returns true for isSame(f,g)), or
   * null if none exist.
   */
  static Node getSymmFact(TNode f);
  /** identify */
  std::string identify() const override;

 protected:
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofNodeMap;
  /** The proof manager, used for allocating new ProofNode objects */
  ProofNodeManager* d_manager;
  /** A dummy context used by this class if none is provided */
  context::Context d_context;
  /** The nodes of the proof */
  NodeProofNodeMap d_nodes;
  /** Get proof for fact, or nullptr if it does not exist. */
  std::shared_ptr<ProofNode> getProof(Node fact) const;
  /** Ensure fact sym */
  std::shared_ptr<ProofNode> getProofSymm(Node fact);
  /**
   * Returns true if we should overwrite proof node pn with a step having id
   * newId, based on policy opol.
   */
  static bool shouldOverwrite(ProofNode* pn, PfRule newId, CDPOverwrite opol);
  /** Returns true if pn is an assumption. */
  static bool isAssumption(ProofNode* pn);
  /**
   * Notify new proof, called when a new proof of expected is provided. This is
   * used internally to connect proofs of symmetric facts, when necessary.
   */
  void notifyNewProof(Node expected);
};

}  // namespace CVC4

#endif /* CVC4__EXPR__PROOF_MANAGER_H */

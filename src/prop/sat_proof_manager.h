/*********************                                                        */
/*! \file sat_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager for Minisat
 **/

#include "cvc4_private.h"

#ifndef CVC4__SAT_PROOF_MANAGER_H
#define CVC4__SAT_PROOF_MANAGER_H

#include "context/cdhashset.h"
#include "expr/buffered_proof_generator.h"
#include "expr/expr.h"
#include "expr/lazy_proof_chain.h"
#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/sat_solver_types.h"

namespace Minisat {
class Solver;
}

namespace CVC4 {
namespace prop {

/**
 * This class is responsible for managing the proof production of the SAT
 * solver. It tracks justifications produce during the solving and stores them
 * independently, only making the connection of the justifications when the
 * empty clause is produced and the refutation is complete. These justifications
 * are stored in a LazyCDProofChain, a user-context-dependent proof that takes
 * lazy steps and can connect them during expansion. Its use in this proof
 * manager is so that, assuming the following lazy steps are saved in the
 * LazyCDProofChain:
 *
 * --- S0: (l4,          PG0)
 * --- S1: ((or l3 l4),  PG1)
 * --- S2: ((or l1 ~l3), PG2)
 * --- S3: (false,       PG3)
 * --- S4: (~l2,         PG4)
 * --- S5: (~l3,         PG5)
 * --- S6: (~l5,         PG6)
 *
 * when requesting the proof for false, assuming that the proof generators have
 * the following expansions:
 *
 * --- PG0 -> (CHAIN_RES ((or l4 l1) ~l1))
 * --- PG1 -> (CHAIN_RES ((or l3 l5 l6 l7 l8) ~l8 (or l4 ~l5) (or ~l6 l7) ~l7))
 * --- PG2 -> (CHAIN_RES ((or l1 ~l3 l5) ~l5))
 * --- PG3 -> (CHAIN_RES ((or l1 l2) ~l1 ~l2))
 * --- PG4 -> (CHAIN_RES ((or l3 ~l2) ~l3))
 * --- PG5 -> (CHAIN_RES ((or l1 ~l3) ~l1))
 * --- PG6 -> (CHAIN_RES ((or l1 ~l5) ~l1))
 *
 * will connect the independent justifications, yielding the following refutation
 *
 *                                             (or l1 ~l5)  ~l1
 *                                             ---------------- CHAIN_RES
 *                            (or l1 ~l3 l5)   ~l5
 *                            ---------------------- CHAIN_RES
 *                                      (or l1 ~l3)            ~l1
 *                                      --------------------------- CHAIN_RES
 *                       (or l3 ~l2)     ~l3
 *                       -------------------- CHAIN_RES
 *   (or l1 l2)     ~l1   ~l2
 *  --------------------------- CHAIN_RES
 *                      false
 *
 * where note that the steps S0 and S1, for l4 and (or l3 l4), respectively,
 * were ignored, since they were not part of the chain starting with
 * false. Moreover there is no sense in the chain of steps being added
 * chronologically. The chain started on step S3 and proceeded to steps S4, S5
 * and S2.
 *
 * To track the reasoning of the SAT solver and produce the steps above this
 * class does three main things:
 *  (1) Register the justifications for learned clauses as they are learned.
 *  (2) Register the justifications for propagated literals when necessary.
 *  (3) Register the *full* justification for the empty clause.
 *
 * Case (1) covers the learned clauses during backjumping. We only information
 * saved is that, from clauses C1 to Cn, a given learned clause C is derived via
 * chain resolution (and possibly factoring, reordering and double negation
 * elimination in its literals), i.e., we do not recursively justify C1 to Cn.
 *
 * Not explaining C1 to Cn eagerly is beneficial because:
 * - we might be wasting resources in fully explanaining it now, since C may not be necessary
 *   for the derivation of the empty clause, or
 * - in explaining lazily we might have a shorter explanation, which has been
 *   observed empirically to be often the case.
 *
 * The latter case is a result of the SAT solver possibly changing the
 * explanation of each of C, C1 to Cn, or the components of their
 * justifications. Since the set of propagated literals that may be used in
 * these derivations can change with the different SAT contexts, the same clause
 * may be derived several times.
 *
 * Therefore we only fully explain a clause when absolutely necessary, i.e.,
 * when we are done (see case (3)) or when we'd not be able to do it afterwards
 * (see case (2)). In the example above, step S2 in an example of case (1), with
 * the shallow proof
 *
 *        (or l1 ~l3 l5)       ~l5
 *        ------------------------- CHAIN_RES
 *                 (or l1 ~l3)
 *
 * justifying the learned clause generated before the refutation is completed.
 *
 * Case (2) covers: the literals propagated from clauses being deleted (2.1);
 * and propagated literals whose negation occurs in a learned clause (2.2),
 * which are then deleted for being redundant.
 *
 * Case (2.1) only happens for the so-called "locked clauses", which are clauses
 * C = l1 v ... v ln that propagate their first literal, l1. When a locked
 * clause C is deleted we save a chain resolution justification of l1 because
 * we'd not be able to retrieve C afterwards, since it is deleted. The
 * justification is a chain resolution between C and ~l2, ..., ~ln, concluding
 * l1. In the example above, step S0 is a result case (2.1),
 *
 * Case (2.2) requires that, when a redundant literal is deleted from a learned
 * clause, we add its negation, which necessarily is a propagated literal, to
 * the justification of the resolution yielding the learned clause. This
 * justifies the deletion of the redundant literal. However, the justification
 * for the propagated literal (the SAT solver maintains a map from propagated
 * literals to the clauses that propagate them in the current context) may also
 * contain literals that were in the learned clause and were deleted for being
 * redundant. Therefore eliminating a redundant literal requires recursively
 * explaining the propagated literals in its justification as long as they are,
 * themselves, redundant literals in the learned clause.
 *
 * Case (3) happens when the SAT solver derives the empty clause and it's not
 * possible to backjump. The empty clause is learned from a conflict clause: a
 * clause whose every literal has its negation propagated in the current
 * context. Thus the justification of the empty clause happens, at first, in the
 * same way as case (1): a resolution chain betweeen the conflict clause and its
 * negated literals. Moreover, since we are now done, we recursively explain the
 * propagated literals, starting from the negated literals from the conflict
 * clause and progressing to all propagated literals ocurring in a given
 * explanation.
 *
 *
 *
 *
 */
class SatProofManager
{
 public:
  SatProofManager(Minisat::Solver* solver,
                  TheoryProxy* proxy,
                  context::UserContext* userContext,
                  ProofNodeManager* pnm);

  /** Marks the start of a resolution chain.
   *
   * The given clause is registered in d_resLinks with a null pivot, since this
   * is the first link in the chain.
   *
   * @param start a SAT solver clause (list of literals) that will be the first
   * clause in a resolution chain.
   */
  void startResChain(const Minisat::Clause& start);
  // resolution with unit clause ~lit, to be justified
  //
  // @param redundant whether lit is redundant, in which case it will be handled
  // differently
  void addResolutionStep(Minisat::Lit lit, bool redundant = false);
  // resolution with clause using lit as pivot. Sign determines whether it's
  // being removed positively from the given clause or the implicit one it's
  // being resolved against
  void addResolutionStep(const Minisat::Clause& clause, Minisat::Lit lit);
  void endResChain(Minisat::Lit lit);
  void endResChain(const Minisat::Clause& clause);

  /**
   * The justification of a literal is built according to its *current*
   * justification in the SAT solver. Thus the proof of the node corresponding
   * to lit is *always* overwritten *unless* that'd result in a cyclic
   * proof. The SAT solver can produce cyclic proofs in instances where literals
   * and clauses coincide, for example
   *
   *  [proof]
   *
   * is cyclic at the node level but not at the SAT solver level. We avoid
   * cyclic proofs by computing, for the justification of a given literal, the
   * necessary assumptions. If the node is in the assumptions, we do not add the
   * resolution step.
   */
  void tryJustifyingLit(
      prop::SatLiteral lit,
      std::unordered_set<TNode, TNodeHashFunction>& assumptions);

  void tryJustifyingLit(prop::SatLiteral lit);

  void finalizeProof(Node inConflictNode,
                     const std::vector<SatLiteral>& inConflict);
  /**
   * @param adding whethen the conflict is coming from a freshly added clause
   */
  void finalizeProof(const Minisat::Clause& inConflict, bool adding = false);
  void finalizeProof(Minisat::Lit inConflict, bool adding = false);
  void finalizeProof();
  void storeUnitConflict(Minisat::Lit inConflict);

  std::shared_ptr<ProofNode> getProof();

  void registerSatLitAssumption(Minisat::Lit lit);
  void registerSatAssumptions(const std::vector<Node>& assumps);

 private:
  void endResChain(Node conclusion, const std::set<SatLiteral>& conclusionLits);

  // If the redundant literal has a reason, we add that as the resolution step,
  // with the redundant literal as resolvent, otherwise it's a step with the
  // negation of the redundant literal as the res step clause.
  //
  // Moreover, if the reason contains literals that do not show up in the
  // conclusion of the resolution chain, they count as redundant literals as
  // well mark literal as redundant
  void processRedundantLit(SatLiteral lit,
                           const std::set<SatLiteral>& conclusionLits,
                           std::set<SatLiteral>& visited,
                           unsigned pos);

  /** The sat solver to which we are managing proofs */
  Minisat::Solver* d_solver;
  /** A pointer to theory proxy */
  TheoryProxy* d_proxy;

  /** The proof node manager */
  ProofNodeManager* d_pnm;

  /** Resolution steps (links) accumulator for chain resolution. Each pair has a
   * clause and the pivot for the resolution step it is involved on. */
  std::vector<std::pair<Node, Node>> d_resLinks;

  /** redundant literals removed from the resolution chain conclusion */
  std::vector<SatLiteral> d_redundantLits;

  /**
   * Associates clauses to their local proofs. These proofs are local and
   * possibly updated during solving. When the final conclusion is reached, a
   * final proof is built based on the proofs saved here.
   */
  LazyCDProofChain d_resChains;

  /** The proof generator for resolution chains */
  BufferedProofGenerator d_resChainPg;

  /** The resolution proof of false */
  CDProof d_proof;

  /** The false node */
  Node d_false;

  /** All clauses added to the SAT solver, kept in a context-dependend manner.
   */
  context::CDHashSet<Node, NodeHashFunction> d_assumptions;

  /**
   * A placeholder that may be used to store the literal with the final
   * conflict
   */
  SatLiteral d_conflictLit;

  Node getClauseNode(SatLiteral satLit);
  Node getClauseNode(const Minisat::Clause& clause);
  void printClause(const Minisat::Clause& clause);
}; /* class SatProofManager */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__SAT_PROOF_MANAGER_H */

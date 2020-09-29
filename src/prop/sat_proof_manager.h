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
#include "prop/cnf_stream.h"
#include "prop/sat_solver_types.h"

namespace Minisat {
class Solver;
}

namespace CVC4 {
namespace prop {

/**
 * This class is responsible for managing the proof production of the SAT
 * solver. It tracks resolutions produced during solving and stores them,
 * independently, with the connection of the resolutions only made when the
 * empty clause is produced and the refutation is complete. The expected
 * assumptions of the refutation are the clausified preprocessed assertions and
 * lemmas.
 *
 * These resolutions are stored in a LazyCDProofChain, a user-context-dependent
 * proof that takes lazy steps and can connect them when generating a proof for
 * a given fact. Its use in this proof manager is so that, assuming the
 * following lazy steps are saved in the LazyCDProofChain:
 *
 * --- S0: (l4,          PG0)
 * --- S1: ((or l3 l4),  PG1)
 * --- S2: ((or l1 ~l3), PG2)
 * --- S3: (false,       PG3)
 * --- S4: (~l2,         PG4)
 * --- S5: (~l3,         PG5)
 * --- S6: (~l5,         PG6)
 *
 * when requesting the proof of false, assuming that the proof generators have
 * the following expansions:
 *
 * --- PG0 -> (CHAIN_RES ((or l4 l1) ~l1))
 * --- PG1 -> (CHAIN_RES ((or l3 l5 l6 l7) ~l5 (or ~l6 l7) (or l4 ~l7)))
 * --- PG2 -> (CHAIN_RES ((or l1 ~l3 l5) ~l5))
 * --- PG3 -> (CHAIN_RES ((or l1 l2) ~l1 ~l2))
 * --- PG4 -> (CHAIN_RES ((or l3 ~l2) ~l3))
 * --- PG5 -> (CHAIN_RES ((or l1 ~l3) ~l1))
 * --- PG6 -> (CHAIN_RES ((or l1 ~l5) ~l1))
 *
 * will connect the independent resolutions and yield the following refutation
 *
 *                                             (or l1 ~l5)  ~l1
 *                                             ---------------- CHAIN_RES
 *                            (or l1 ~l3 l5)   ~l5
 *                            ---------------------- CHAIN_RES
 *                                      (or l1 ~l3)              ~l1
 *                                      ----------------------------- CHAIN_RES
 *                       (or l3 ~l2)     ~l3
 *                       -------------------- CHAIN_RES
 *   (or l1 l2)   ~l1    ~l2
 *  --------------------------- CHAIN_RES
 *              false
 *
 * where note that the steps S0 and S1, for l4 and (or l3 l4), respectively,
 * were ignored, since they were not part of the chain starting with
 * false. Moreover there is no requirement that the steps are registered
 * chronologically in the LazyCDProofChain. The chain started on step S3 and
 * proceeded to steps S4, S5, S2, and finally S6.
 *
 * To track the reasoning of the SAT solver and produce the steps above this
 * class does three main things:
 *  (1) Register the resolutions for learned clauses as they are learned.
 *  (2) Register the resolutions for propagated literals when necessary.
 *  (3) Register the *full* resolution proof for the empty clause.
 *
 * Case (1) covers the learned clauses during backjumping. The only information
 * saved is that, from clauses C1 to Cn, a given learned clause C is derived via
 * chain resolution (and possibly factoring, reordering and double negation
 * elimination in its literals), i.e., we do not recursively prove C1 to Cn at
 * this moment.
 *
 * Not explaining C1 to Cn eagerly is beneficial because:
 * - we might be wasting resources in fully explanaining it now, since C may not
 *   be necessary for the derivation of the empty clause, and
 * - in explaining clauses lazily we might have shorter explanations, which has
 *   been observed empirically to be often the case.
 *
 * The latter case is a result of the SAT solver possibly changing the
 * explanation of each of C, C1 to Cn, or the components of their
 * explanations. This is because the set of propagated literals that may be used
 * in these explanations can change in different SAT contexts, with the same
 * clause being derived several times, each from a different set of clauses.
 *
 * Therefore we only fully explain a clause when absolutely necessary, i.e.,
 * when we are done (see case (3)) or when we'd not be able to do it afterwards
 * (see case (2)). In the example above, step S2 is generated from case (1),
 * with the shallow proof
 *
 *        (or l1 ~l3 l5)       ~l5
 *        ------------------------- CHAIN_RES
 *                 (or l1 ~l3)
 *
 * explaining the learned clause (or l1 ~l3). Its full proof would only be
 * produced if it were part of the final refutation, as it indeed is. Note that
 * in the example above the refutation proof contains the resolution proof of
 * ~l5.
 *
 * Case (2) covers:
 *  (2.1) propagated literals explained by clauses being deleted
 *  (2.2) propagated literals whose negation occurs in a learned clause, which
 *  are then deleted for being redundant.
 *
 * Case (2.1) only happens for the so-called "locked clauses", which are clauses
 * C = l1 v ... v ln that propagate their first literal, l1. When a locked
 * clause C is deleted we save a chain resolution proof of l1 because we'd not
 * be able to retrieve C afterwards, since it is deleted. The proof is a chain
 * resolution step between C and ~l2, ..., ~ln, concluding l1. In the example
 * above, step S0 is generated from case (2.1), with the locked clause (or l4
 * l1) being deleted and requiring the registration in the LazyCDPRoofChain of a
 * lazy step for
 *
 *         (or l4 l1)       ~l1
 *      ------------------------- CHAIN_RES
 *               l4
 *
 * Case (2.2) requires that, when a redundant literal (i.e., a literal whose
 * negation is propagated) is deleted from a learned clause, we add the
 * explanation of its negation to the chain resolution proof of the learned
 * clause. This justifies the deletion of the redundant literal. However, the
 * explanation for the propagated literal (the SAT solver maintains a map from
 * propagated literals to the clauses that propagate them in the current
 * context, i.e., their explanations, clauses in which all literals but the
 * propagated one have their negation propagated) may also contain literals that
 * were in the learned clause and were deleted for being redundant. Therefore
 * eliminating a redundant literal requires recursively explaining the
 * propagated literals in its explanation as long as they are, themselves,
 * redundant literals in the learned clause.
 *
 * In the above example step S1, concluding (or l3 l4), is generated from the
 * resolutions
 *
 *   (or l3 l5 l6 l7)    ~l5
 *  -------------------------- CHAIN_RES
 *     (or l3 l6 l7)                        (or ~l6 l7)   (or l4 ~l7)
 *    ---------------------------------------------------------------- CHAIN_RES
 *                           (or l3 l4)
 *
 * as l6 and l7 are redundant, which leads to (or l3 l6 l7) being resolved with
 * l6's explanation, (or ~l6 l7). The literals in the explanation of l7 are
 * recursively explained if they are also redundant, which is the case for l7,
 * so its explanation is also added as premise for the resolution. Since l4 is
 * not redundant, it is not recursively explained.
 *
 * Note that the actual proof generated does not have the intermediary step
 * before removing redundant literals. It's all done in one fell swoop:
 *
 *   (or l3 l5 l6 l7)   ~l5   (or ~l6 l7)   (or l4 ~l7)
 *   --------------------------------------------------- CHAIN_RES
 *                           (or l3 l4)
 *
 * Finally, case (3) happens when the SAT solver derives the empty clause and
 * it's not possible to backjump. The empty clause is learned from a conflict
 * clause: a clause whose every literal has its negation propagated in the
 * current context. Thus the proof of the empty clause is generated, at first,
 * in the same way as case (1): a resolution chain betweeen the conflict clause
 * and its negated literals. However, since we are now done, we recursively
 * explain the propagated literals, starting from the negated literals from the
 * conflict clause and progressing to all propagated literals ocurring in a
 * given explanation.
 *
 * In the above example this happens as: step S3
 *
 *    (or l1 l2)   ~l1    ~l2
 *  --------------------------- CHAIN_RES
 *             false
 *
 * is added for a conflict clause (or l1 l2). Then we attempt to explain ~l1 and
 * ~l2. The former has no explanation (i.e., it's an input), while the latter
 * has explanation (or l3 ~l2). This leads to step S4
 *
 *  (or l3 ~l2)     ~l3
 *  -------------------- CHAIN_RES
 *        ~l2
 *
 * being added to the LazyCDProofChain. In explaining ~l3 the step S5
 *
 *  (or l1 ~l3)      ~l1
 *  --------------------- CHAIN_RES
 *         ~l3
 *
 * is added. Since ~l1 has no explanation, the process halts. Note that at this
 * point the step S6 has not been added to the LazyCDProofChain. This is because
 * to explain ~l5 we need to look at the literal premises in the proofs of
 * learned clauses.
 *
 * The last thing done then in case (3), after the resolution on the conflict
 * clause and an initial recursive explanation of propagated literals, is to
 * connect the refutation proof and then recursively its propagated literal
 * leaves, repeating until a fix point.
 *
 * In the above example the first connection yields
 *
 *                           (or l1 ~l3 l5)   ~l5
 *                           ---------------------- CHAIN_RES
 *                                     (or l1 ~l3)              ~l1
 *                                     ----------------------------- CHAIN_RES
 *                      (or l3 ~l2)     ~l3
 *                      -------------------- CHAIN_RES
 *  (or l1 l2)   ~l1    ~l2
 * --------------------------- CHAIN_RES
 *                     false
 *
 * whose literal leaves are ~l1 and ~l5. The former has no explanation, but the
 * latter is explained by (or l1 ~l5), thus leading to step S6
 *
 *  (or l1 ~l5)      ~l1
 *  --------------------- CHAIN_RES
 *         ~l5
 *
 * then the final connection
 *
 *                                             (or l1 ~l5)  ~l1
 *                                             ---------------- CHAIN_RES
 *                            (or l1 ~l3 l5)   ~l5
 *                            ---------------------- CHAIN_RES
 *                                      (or l1 ~l3)              ~l1
 *                                      ----------------------------- CHAIN_RES
 *                       (or l3 ~l2)     ~l3
 *                       -------------------- CHAIN_RES
 *   (or l1 l2)   ~l1    ~l2
 *  --------------------------- CHAIN_RES
 *                      false
 *
 * which has no more explainable literals as leaves.
 *
 * The interfaces below provide ways for the SAT solver to register its
 * assumptions (clausified assertions and lemmas) for the SAT proof
 * (registerSatAssumption), register resolution steps (startResChain /
 * addResolutionStep / endResChain), build the final refutation proof
 * (finalizeProof) and retrieve the refutation proof (getProof). So in a given
 * run of the SAT solver these interfaces are expected to be used in the
 * following order:
 *
 * (registerSatAssumptions | (startResChain (addResolutionStep)+ endResChain)*)*
 * finalizeProof
 * getProof
 *
 */
class SatProofManager
{
 public:
  SatProofManager(Minisat::Solver* solver,
                  CnfStream* cnfStream,
                  context::UserContext* userContext,
                  ProofNodeManager* pnm);

  /** Marks the start of a resolution chain.
   *
   * This call is followed by *at least one* call to addResolution step and one
   * call to endResChain.
   *
   * The given clause, at the node level, is registered in d_resLinks with a
   * null pivot, since this is the first link in the chain.
   *
   * @param start a SAT solver clause (list of literals) that will be the first
   * clause in a resolution chain.
   */
  void startResChain(const Minisat::Clause& start);
  /** Adds a resolution step with a clause
   *
   * There must have been a call to startResChain before any call to
   * addResolution step. After following calls to addResolution step there is
   * one call to endResChain.
   *
   * The resolution step is added to d_resLinks with the clause, at the node
   * level, and the literal, at the node level, as the pivot.
   *
   * @param clause the clause being resolved against
   * @param lit the pivot of the resolution step
   */
  void addResolutionStep(const Minisat::Clause& clause, Minisat::Lit lit);
  /** Adds a resolution step with a unit clause
   *
   * The resolution step is added to d_resLinks such that lit, at the node
   * level, is the pivot and and the unit clause is ~lit, at the node level.
   *
   * If the literal is marked as redundant, then a step is *not* is added to
   * d_resLinks. It is rather saved to d_redundandLits, whose components we will
   * be handled in a special manner when the resolution chain is finished. This
   * is because the steps corresponding to the removal of redundant literals
   * have to be done in a specific order. See proccessRedundantLits below.
   *
   * @param lit the literal being resolved against
   * @param redundant whether lit is redundant
   */
  void addResolutionStep(Minisat::Lit lit, bool redundant = false);
  /** Ends resolution chain concluding a unit clause
   *
   * This call must have been preceded by one call to startResChain and at least
   * one call to addResolutionStep.
   *
   * This and the version below both call the node version of this method,
   * described further below, which actually does the necessary processing.
   */
  void endResChain(Minisat::Lit lit);
  /** Ends resolution chain concluding a clause */
  void endResChain(const Minisat::Clause& clause);
  /** Build refutation proof starting from conflict clause
   *
   * This method (or its variations) is only called when the SAT solver has
   * reached an unsatisfiable state.
   *
   * This and the versions below call the node version of this method, described
   * further below, which actually does the necessary processing.
   *
   * @param adding whether the conflict is coming from a freshly added clause
   */
  void finalizeProof(const Minisat::Clause& inConflict, bool adding = false);
  /** Build refutation proof starting from conflict unit clause
   *
   * @param adding whether the conflict is coming from a freshly added clause
   */
  void finalizeProof(Minisat::Lit inConflict, bool adding = false);
  /** As above, but uses the unit conflict clause saved in d_conflictLit. */
  void finalizeProof();
  /** Set the unit conflict clause d_conflictLit. */
  void storeUnitConflict(Minisat::Lit inConflict);

  /** Retrive the refutation proof
   *
   * If there is no chain for false in d_resChains, meaning that this call was
   * made before finalizeProof, an assumption proof node is produced.
   */
  std::shared_ptr<ProofNode> getProof();

  /** Register a unit clause input, converted to its node representation.  */
  void registerSatLitAssumption(Minisat::Lit lit);
  /** Register a set clause inputs. */
  void registerSatAssumptions(const std::vector<Node>& assumps);

 private:
  /** Ends resolution chain concluding clause
   *
   * This method builds the proof of conclusion from the resolution chain
   * currently saved in d_resLinks.
   *
   * First each saved redundant literals in d_redundantLits is processed via
   * processRedundantLit. The literals in the resolution chain's conclusion are
   * used to verifynig which literals in the computed explanations are
   * redundant, i.e., don't occur in conclusionLits. The nessary resolution
   * steps will be added to d_resLinks.
   *
   * The proof to be built will be a CHAIN_RESOLUTION step, whose children and
   * arguments will be retrieved from traversing d_resLinks. Consider the
   * following d_resLinks (where each [~]li is its node equivalent):
   *
   * - <(or l3 l5 l6 l7), null>
   * - <~l5, l5>
   * - <(or ~l6 l7), l6>
   * - <(or l4 ~l7), l7>
   *
   * The resulting children and arguments for the CHAIN_RESOLUTION proof step would be:
   * - [(or l3 l5 l6 l7), ~l5, (or ~l6 l7), (or l4 ~l7)]
   * - [l5, l6, l7]
   * and the proof step
   *
   *   (or l3 l5 l6 l7)   ~l5   (or ~l6 l7)   (or l4 ~l7)
   *   --------------------------------------------------- CHAIN_RES_{l5,l6,l7}
   *                           (or l3 l4)
   *
   * The conclusion of the CHAIN_RES proof step is *not* the given conclusion of
   * this method. This is because conclusion is the node equivalent of the
   * clause in the SAT solver, which is kept modulo duplicates, reordering, and
   * double negation elimination. Therefore we generate the above step in the
   * correct way for the semantics of CHAIN_RES, based on its children and
   * arguments, via the d_pnm's proof checker. The resulting node n is fed into
   * the clause normalization in TheoryProofStepBuffer, which reduces n to
   * conclusion.
   *
   * All the proof steps generated to conclude conclusion from the premises in
   * d_resLinks are saved into d_resChainPg, which is saved as the proof
   * generator for lazy step added to d_resChains for the conclusion.
   *
   * @param conclusion the node-level conclusion of the resolution chain
   * @param conclusionLits the set of literals in the conclusion
   */
  void endResChain(Node conclusion, const std::set<SatLiteral>& conclusionLits);

  /** Explain redundant literal and generate corresponding resolution steps
   *
   * If the redundant literal has a reason, we add a resolution step with that
   * clause, otherwise with the negation of the redundant literal as the unit
   * clause. The redundant literal is the resolvent in both cases.  The steps
   * are always added as the *first* link after last resolution step added
   * *before* processing redundant literals began, i.e., at d_resLinks.begin() +
   * pos. This is to guarantee that the links are in the correct order for the
   * chain resolution, see below.
   *
   * If the reason contains literals that do not occur in conclusionLits, they
   * are redundant and recursively processed by this method. This recursive
   * processing happens *before* the resolution step for lit is added. Since
   * steps are always added in position pos, pushing steps after that 1
   * position, this guarantees that a step with a clause will occur before the
   * steps that eliminate its redundant literals.
   *
   * Consider d_resLinks with 3 links before the first processRedundantLit call,
   * i.e., pos = 3, and d_redundantLits = {l1}, with reason(l1) = (or l1 ~l2),
   * with ~l2 redundant. Assume ~l2 has no explanation. By processing ~l2 first,
   * the link <~l2, l2> will be added at position 3. Then by coming back to the
   * processing of l1 the link <(or l1 ~l2), l1> will also be added position 3,
   * with <~l2, l2> pushed to position 4. If this these links had the reverse
   * order the literal ~l2 would, erroneously, occur in the chain resolution
   * conclusion, as it is introduced by (or l1 ~l2).
   *
   * After a resolution step for a redundant literal is added, it is marked as
   * visited, thus avoiding adding redundunt resolution steps to the chain if
   * that literal occurs again in another redundant literal's reason.
   *
   * @param lit the redundant literal
   * @param conclusionLits the literals in the clause from which redundant
   * literals have been removed
   * @param visited cache of literals already processed
   * @param pos position, in d_resLinks, of last resolution step added *before*
   * processing redundant literals
   */
  void processRedundantLit(SatLiteral lit,
                           const std::set<SatLiteral>& conclusionLits,
                           std::set<SatLiteral>& visited,
                           unsigned pos);
  /** Explain literal if it is propagated in the SAT solver
   *
   * If a literal is propagated, i.e., it has a reason in the SAT solver, that
   * clause is retrieved. This method is then called recursively on the negation
   * of each of reason's literals (that is not lit). Afterwards a
   * CHAIN_RESOLUTION proof step is created to conclude lit from the reason and
   * its literals, other than lit, negations.
   *
   * This method also tracks all the literals and clauses, at the node level,
   * that have been used as premises of resolutions steps in the recursive
   * explanations. A resolution step is only created if the conclusion does not
   * occur in these premises, as this would configure a cyclic proof.
   *
   * These cyclic proofs, at the node level, are naturally generated by the SAT
   * solver because they are so that a literal is derived from a clause (so they
   * are different) but both correspond to the *same node*. For example,
   * consider the following derivation at the SAT solver level
   *
   *                       [l1, l2, l3]    ~l2   ~l3
   *                       -------------------------- CHAIN_RES
   *           [l0, ~l1]       l1
   *           ---------------------- CHAIN_RES
   *                    l0
   *
   * which has no issues. However, its node equivalent is
   *
   *                  (or a b c)    (not b)   (not c)
   *                  ------------------------------- CHAIN_RES
   *      (or (or a b c) (not a))       a
   *      --------------------------------- CHAIN_RES
   *               (or a b c)
   *
   * which is cyclic. The issue is that l0 = (or a b c). Only at the SAT level
   * are l0 and [l1, l2, l3] different.
   *
   * If a cyclic proof is identified, the respective node is kept as an
   * assumption.
   *
   * @param lit the literal to explained
   * @param premises set of literals and clauses, at the node level, that
   * have been used as premises of resolution steps while explaining
   * propagations
   */
  void explainLit(prop::SatLiteral lit,
                  std::unordered_set<TNode, TNodeHashFunction>& premises);

  /** Build refutation proof starting from conflict clause
   *
   * Given a conflict clause, this method handles case (3) described in the
   * preamble. Each of the literals in the conflict clause is either
   * explainable, the result of a previously saved resolution chain, or an
   * input.
   *
   * First, explainLit is called recursively on the negated literals from
   * the conflict clause.
   *
   * Second, a CHAIN_RESOLUTION proof step is added between
   * the conflict clause and its negated literals, concluding false.
   *
   * Third, until a fix point, the refutation proof is connected, by calling
   * d_resChain.getProofFor(d_false), its free assumptions are determined and,
   * in case any as a literal that might be explained, we call explainLit.
   *
   * The latter is called to a fix point because adding an explanation to a
   * propagated literal may connect it with a previously saved resolution chain,
   * which may have free assumptions that are literals that can be explained and
   * so on.
   *
   * @param inConflictNode node corresponding to conflict clause
   * @param inConflict literals in the conflict clause
   */
  void finalizeProof(Node inConflictNode,
                     const std::vector<SatLiteral>& inConflict);

  /** The SAT solver to which we are managing proofs */
  Minisat::Solver* d_solver;
  /** Pointer to the underlying cnf stream. */
  CnfStream* d_cnfStream;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** Resolution steps (links) accumulator for chain resolution.
   *
   * Each pair has a clause and the pivot for the resolution step it is involved
   * on. The pivot occurs positively in the clause yielded by the resolution up
   * to the previous link and negatively in this link. The first link has a null
   * pivot. Links are kept at the node level.
   *
   * This accumulator is reset after each chain resolution. */
  std::vector<std::pair<Node, Node>> d_resLinks;

  /** Redundant literals removed from the resolution chain's conclusion.
   *
   * This accumulator is reset after each chain resolution. */
  std::vector<SatLiteral> d_redundantLits;

  /**
   * Associates clauses to their local proofs. These proofs are local and
   * possibly updated during solving. When the final conclusion is reached, a
   * final proof is built based on the proofs saved here.
   *
   * This chain is initialized so that its getProofFor method, which connects
   * the chain, accounts for cyclic proofs. This is so that we avoid the issue
   * described in explainLit.
   */
  LazyCDProofChain d_resChains;

  /** The proof generator for resolution chains */
  BufferedProofGenerator d_resChainPg;

  /** The false node */
  Node d_false;

  /** All clauses added to the SAT solver, kept in a context-dependent manner.
   */
  context::CDHashSet<Node, NodeHashFunction> d_assumptions;

  /**
   * A placeholder that may be used to store the literal with the final
   * conflict.
   */
  SatLiteral d_conflictLit;
  /** Gets node equivalent to literal */
  Node getClauseNode(SatLiteral satLit);
  /** Gets node equivalent to clause.
   *
   * To avoid generating different nodes for the same clause, modulo ordering,
   * an invariant assumed throughout this class, the OR node generated by this
   * method always has its children ordered.
   */
  Node getClauseNode(const Minisat::Clause& clause);
  /** Prints clause, as a sequence of literals, in the "sat-proof" trace. */
  void printClause(const Minisat::Clause& clause);
}; /* class SatProofManager */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__SAT_PROOF_MANAGER_H */

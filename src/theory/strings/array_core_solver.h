/******************************************************************************
 * Top contributors (to current version):
 *   Ying Sheng, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Sequences solver for seq.nth/seq.update.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__ARRAY_CORE_SOLVER_H
#define CVC5__THEORY__STRINGS__ARRAY_CORE_SOLVER_H

#include "theory/strings/core_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/inference_manager.h"
#include "theory/strings/solver_state.h"
#include "theory/strings/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

class ArrayCoreSolver : protected EnvObj
{
 public:
  ArrayCoreSolver(Env& env,
                  SolverState& s,
                  InferenceManager& im,
                  TermRegistry& tr,
                  CoreSolver& cs,
                  ExtfSolver& es,
                  ExtTheory& extt);
  ~ArrayCoreSolver();

  /**
   * Perform reasoning about seq.nth and seq.update operations.
   *
   * Can assume that seq.update / seq.nth terms only apply to concatenation-free
   * equivalence classes.
   */
  void check(const std::vector<Node>& nthTerms,
             const std::vector<Node>& updateTerms);

  /**
   *
   * @param eqc The sequence equivalence class representative. We can assume
   * the equivalence class of eqc contains no concatenation terms.
   * @return the map corresponding to the model for eqc. The domain of
   * the returned map should be in distinct integer equivalence classes of the
   * equality engine of strings theory. The model assigned to eqc will be
   * a skeleton constructed via seq.++ where the components take values from
   * this map.
   */
  const std::map<Node, Node>& getWriteModel(Node eqc);

  /**
   * Get connected sequences, see documentation of computeConnected.
   * @return a map M such that sequence equivalence class representatives x and
   * y are connected if an only if M[x] = M[y].
   */
  const std::map<Node, Node>& getConnectedSequences();

 private:
  void sendInference(const std::vector<Node>& exp,
                     const Node& lem,
                     const InferenceId iid,
                     bool asLemma = false);

  /**
   * Perform reasoning about seq.nth operation.
   * It handled the reduction from seq.extract to seq.nth, following the rule
   * below: (t = (seq.extract A i 1)) ^ (0 <= i) ^ (i < (str.len A))
   * ----------------------------------------------------------------------
   * t = (seq.unit (seq.nth A i))
   */
  void checkNth(const std::vector<Node>& nthTerms);

  /**
   * Perform reasoning about seq.update operation.
   * It handled the reduction from seq.update to seq.nth, following the rule
   * below: (seq.update x i a) in TERMS (seq.nth t j) in TERMS t == (seq.update
   * x i a)
   * ----------------------------------------------------------------------
   * (seq.nth (seq.update x i a) j) = (ITE, j in range(i, i+len(a)), (seq.nth a
   * (j - i)), (seq.nth x j))
   */
  void checkUpdate(const std::vector<Node>& updateTerms);

  /**
   * Given the current set of update terms, this computes the connected
   * sequences implied by the current equality information + this set of terms.
   * Connected sequences is a reflexive transitive relation where additionally
   * a and b are connected if there exists an update term (seq.update a n x)
   * that is currently equal to b.
   *
   * This method runs a union find algorithm to compute all connected sequences.
   *
   * As a result of running this method, the map d_connectedSeq is populated
   * with information regarding which sequences are connected.
   */
  void computeConnected(const std::vector<Node>& updateTerms);

  /** The solver state object */
  SolverState& d_state;
  /** The (custom) output channel of the theory of strings */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of strings */
  TermRegistry& d_termReg;
  /** reference to the core solver, used for certain queries */
  CoreSolver& d_csolver;
  /** reference to the extended solver, used for certain queries */
  ExtfSolver& d_esolver;
  /** the extended theory object for the theory of strings */
  ExtTheory& d_extt;
  /** The write model */
  std::map<Node, std::map<Node, Node>> d_writeModel;
  /**
   * Map from sequences to their "connected representative". Two sequences are
   * connected (based on the definition described in computeConnected) iff they
   * have the same connected representative. Sequences that do not occur in
   * this map are assumed to be their own connected representative.
   *
   * This map is only valid after running computeConnected, and is valid
   * only during model building.
   */
  std::map<Node, Node> d_connectedSeq;
  /** The set of lemmas been sent */
  context::CDHashSet<Node> d_lem;
  /** Set of updates that have been registered */
  context::CDHashSet<Node> d_registeredUpdates;

  // ========= data structure =========
  /** Map sequence variable to indices that occurred in nth terms */
  std::map<Node, std::set<Node>> d_indexMap;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif

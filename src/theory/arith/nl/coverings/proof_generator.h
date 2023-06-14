/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the proof generator for coverings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_GENERATOR_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_GENERATOR_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"
#include "proof/lazy_tree_proof_generator.h"
#include "proof/proof_set.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/coverings/cdcac_utils.h"

namespace cvc5::internal {

class ProofGenerator;

namespace theory {
namespace arith {
namespace nl {

struct VariableMapper;

namespace coverings {

/**
 * This class manages the proof creation during a run of the coverings solver.
 *
 * Though it implements the ProofGenerator interface getProofFor(Node), it only
 * gives a proof for a single node.
 *
 * It uses a LazyTreeProofGenerator internally to manage the tree-based proof
 * construction.
 */
class CoveringsProofGenerator : protected EnvObj
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const CoveringsProofGenerator& proof);
  CoveringsProofGenerator(Env& env, context::Context* ctx);

  /** Start a new proof in this proof generator */
  void startNewProof();
  /** Start a new recursive call */
  void startRecursive();
  /** Finish the current recursive call */
  void endRecursive(size_t intervalId);
  /** Start a new scope, corresponding to a guess in CDCAC */
  void startScope();
  /** Finish a scope and add the (generalized) sample that was refuted */
  void endScope(const std::vector<Node>& args);
  /** Return the current proof generator */
  ProofGenerator* getProofGenerator() const;

  /**
   * Calls LazyTreeProofGenerator::pruneChildren(f), but decorates the
   * predicate such that f only accepts the index.
   * @param f A Callable bool(std::size_t)
   */
  template <typename F>
  void pruneChildren(F&& f)
  {
    d_current->pruneChildren([&f](const detail::TreeProofNode& tpn) {
      // The direct children of recursive rules are scopes, but the ids are
      // attached to their children
      if (tpn.d_rule == PfRule::SCOPE && tpn.d_children.size() == 1)
      {
        return f(tpn.d_children[0].d_objectId);
      }
      return f(tpn.d_objectId);
    });
  }

  /**
   * Add a direct interval conflict as generated in getUnsatIntervals().
   * Its meaning is:
   *   over the partial assignment a, var is not in interval because p~sc~0
   *   and the origin of this is constraint.
   *
   * @param var The variable for which the interval is excluded
   * @param vm A variable mapper between cvc5 and libpoly variables
   * @param p The polynomial of the constraint
   * @param a The current partial assignment
   * @param sc The sign condition of the constraint
   * @param interval The concrete interval that is excluded
   * @param constraint The assumption that yields p and sc
   */
  void addDirect(Node var,
                 VariableMapper& vm,
                 const poly::Polynomial& p,
                 const poly::Assignment& a,
                 poly::SignCondition& sc,
                 const poly::Interval& interval,
                 Node constraint,
                 size_t intervalId);

  /**
   * Constructs the (generalized) interval that is to be excluded from a
   * CACInterval. It should be called after the recursive call to construct the
   * generalized sample necessary for endScope().
   *
   * @param var The variable for which the interval is excluded
   * @param i The concrete interval that is excluded
   * @param a The current partial assignment
   * @param s The sample point that is refuted for var
   * @param vm A variable mapper between cvc5 and libpoly variables
   */
  std::vector<Node> constructCell(Node var,
                                  const CACInterval& i,
                                  const poly::Assignment& a,
                                  const poly::Value& s,
                                  VariableMapper& vm);

 private:
  /** The list of generated proofs */
  CDProofSet<LazyTreeProofGenerator> d_proofs;
  /** The current proof */
  LazyTreeProofGenerator* d_current;

  /** Constant false */
  Node d_false;
  /** Constant zero */
  Node d_zero;
};

/**
 * Prints the underlying LazyTreeProofGenerator. Please check the documentation
 * of std::ostream& operator<<(std::ostream&, const LazyTreeProofGenerator&)
 */
std::ostream& operator<<(std::ostream& os, const CoveringsProofGenerator& proof);

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif

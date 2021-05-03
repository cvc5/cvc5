/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the proof generator for CAD.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__CAD__PROOF_GENERATOR_H
#define CVC5__THEORY__ARITH__NL__CAD__PROOF_GENERATOR_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <vector>

#include "expr/node.h"
#include "expr/proof_set.h"
#include "theory/arith/nl/cad/cdcac_utils.h"
#include "theory/lazy_tree_proof_generator.h"

namespace cvc5 {

class ProofGenerator;

namespace theory {
namespace arith {
namespace nl {

struct VariableMapper;

namespace cad {

/**
 * This class manages the proof creation during a run of the CAD solver.
 *
 * Though it implements the ProofGenerator interface getProofFor(Node), it only
 * gives a proof for a single node.
 *
 * It uses a LazyTreeProofGenerator internally to manage the tree-based proof
 * construction.
 */
class CADProofGenerator
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const CADProofGenerator& proof);
  CADProofGenerator(context::Context* ctx, ProofNodeManager* pnm);

  /** Start a new proof in this proof generator */
  void startNewProof();
  /** Start a new recursive call */
  void startRecursive();
  /** Finish the current recursive call */
  void endRecursive();
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
    d_current->pruneChildren(
        [&f](std::size_t i, const detail::TreeProofNode& tpn) { return f(i); });
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
                 Node constraint);

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
  /** The proof node manager used for the proofs */
  ProofNodeManager* d_pnm;
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
std::ostream& operator<<(std::ostream& os, const CADProofGenerator& proof);

}  // namespace cad
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5

#endif
#endif

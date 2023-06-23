/******************************************************************************
 * Top contributors (to current version):
 *   Dejan Jovanovic, Mathias Preiner, Liana Hadarean
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * SAT Solver.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__SAT_SOLVER_H
#define CVC5__PROP__SAT_SOLVER_H

#include <string>

#include "context/cdlist.h"
#include "context/context.h"
#include "expr/node.h"
#include "proof/clause_id.h"
#include "proof/proof_node_manager.h"
#include "prop/sat_solver_types.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {

namespace prop {

class TheoryProxy;

class SatSolver {

public:

  /** Virtual destructor */
  virtual ~SatSolver() { }

  /** Assert a clause in the solver. */
  virtual ClauseId addClause(SatClause& clause,
                             bool removable) = 0;

  /** Return true if the solver supports native xor resoning */
  virtual bool nativeXor() { return false; }

  /** Add a clause corresponding to rhs = l1 xor .. xor ln  */
  virtual ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) = 0;

  /**
   * Create a new boolean variable in the solver.
   * @param isTheoryAtom is this a theory atom that needs to be asserted to
   * theory
   * @param canErase whether the sat solver can safely eliminate this variable
   *
   */
  virtual SatVariable newVar(bool isTheoryAtom, bool canErase) = 0;

  /** Create a new (or return an existing) boolean variable representing the constant true */
  virtual SatVariable trueVar() = 0;

  /** Create a new (or return an existing) boolean variable representing the constant false */
  virtual SatVariable falseVar() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatValue solve() = 0;

  /** Check the satisfiability of the added clauses */
  virtual SatValue solve(long unsigned int&) = 0;

  /** Check satisfiability under assumptions */
  virtual SatValue solve(const std::vector<SatLiteral>& assumptions)
  {
    Unimplemented() << "Solving under assumptions not implemented";
    return SAT_VALUE_UNKNOWN;
  };

  /**
   * Tell SAT solver to only do propagation on next solve().
   *
   * @return true if feature is supported, otherwise false.
   */
  virtual bool setPropagateOnly() { return false; }

  /** Interrupt the solver */
  virtual void interrupt() = 0;

  /** Call value() during the search.*/
  virtual SatValue value(SatLiteral l) = 0;

  /** Call modelValue() when the search is done.*/
  virtual SatValue modelValue(SatLiteral l) = 0;

  /** Get the current assertion level */
  virtual uint32_t getAssertionLevel() const = 0;

  /** Check if the solver is in an inconsistent state */
  virtual bool ok() const = 0;

  /**
   * Get list of unsatisfiable assumptions.
   *
   * The returned assumptions are a subset of the assumptions provided to
   * the solve method.
   * Can only be called if satisfiability check under assumptions was used and
   * if it returned SAT_VALUE_FALSE.
   */
  virtual void getUnsatAssumptions(std::vector<SatLiteral>& unsat_assumptions)
  {
    Unimplemented() << "getUnsatAssumptions not implemented";
  }

};/* class SatSolver */

class CDCLTSatSolver : public SatSolver
{
 public:
  virtual ~CDCLTSatSolver(){};

  virtual void initialize(context::Context* context,
                          prop::TheoryProxy* theoryProxy,
                          context::UserContext* userContext,
                          ProofNodeManager* pnm) = 0;

  virtual void push() = 0;

  virtual void pop() = 0;

  /*
   * Reset the decisions in the DPLL(T) SAT solver at the current assertion
   * level.
   */
  virtual void resetTrail() = 0;

  virtual void requirePhase(SatLiteral lit) = 0;

  virtual bool isDecision(SatVariable decn) const = 0;

  /**
   * Return whether variable has a fixed assignment.
   */
  virtual bool isFixed(SatVariable var) const = 0;

  /**
   * Return the current list of decisions made by the SAT solver.
   */
  virtual std::vector<SatLiteral> getDecisions() const = 0;

  /**
   * Return the order heap of the SAT solver, which is a priority queueue
   * of literals ordered with respect to variable activity.
   */
  virtual std::vector<Node> getOrderHeap() const = 0;

  virtual std::shared_ptr<ProofNode> getProof() = 0;

}; /* class CDCLTSatSolver */

inline std::ostream& operator <<(std::ostream& out, prop::SatLiteral lit) {
  out << lit.toString();
  return out;
}

inline std::ostream& operator <<(std::ostream& out, const prop::SatClause& clause) {
  out << "clause:";
  for(unsigned i = 0; i < clause.size(); ++i) {
    out << " " << clause[i];
  }
  out << ";";
  return out;
}

inline std::ostream& operator <<(std::ostream& out, prop::SatValue val) {
  std::string str;
  switch(val) {
  case prop::SAT_VALUE_UNKNOWN:
    str = "_";
    break;
  case prop::SAT_VALUE_TRUE:
    str = "1";
    break;
  case prop::SAT_VALUE_FALSE:
    str = "0";
    break;
  default:
    str = "Error";
    break;
  }

  out << str;
  return out;
}

}  // namespace prop
}  // namespace cvc5::internal

#endif /* CVC5__PROP__SAT_MODULE_H */

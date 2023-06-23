/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Liana Hadarean, Dejan Jovanovic
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
 *
 * Implementation of the minisat interface for cvc5.
 */

#pragma once

#include "prop/minisat/simp/SimpSolver.h"
#include "prop/sat_solver.h"
#include "smt/env_obj.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {

template <class Solver>
prop::SatLiteral toSatLiteral(typename Solver::TLit lit);

template <class Solver>
void toSatClause(const typename Solver::TClause& minisat_cl,
                 prop::SatClause& sat_cl);

namespace prop {

class MinisatSatSolver : public CDCLTSatSolver, protected EnvObj
{
 public:
  MinisatSatSolver(Env& env, StatisticsRegistry& registry);
  ~MinisatSatSolver() override;

  static SatVariable     toSatVariable(Minisat::Var var);
  static Minisat::Lit    toMinisatLit(SatLiteral lit);
  static SatLiteral      toSatLiteral(Minisat::Lit lit);
  static SatValue        toSatLiteralValue(Minisat::lbool res);
  static Minisat::lbool  toMinisatlbool(SatValue val);
  //(Commented because not in use) static bool            tobool(SatValue val);

  static void  toMinisatClause(SatClause& clause, Minisat::vec<Minisat::Lit>& minisat_clause);
  static void  toSatClause    (const Minisat::Clause& clause, SatClause& sat_clause);
  void initialize(context::Context* context,
                  TheoryProxy* theoryProxy,
                  context::UserContext* userContext,
                  ProofNodeManager* pnm) override;

  ClauseId addClause(SatClause& clause, bool removable) override;
  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override
  {
    Unreachable() << "Minisat does not support native XOR reasoning";
  }

  SatVariable newVar(bool isTheoryAtom, bool canErase) override;
  SatVariable trueVar() override { return d_minisat->trueVar(); }
  SatVariable falseVar() override { return d_minisat->falseVar(); }

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;
  void getUnsatAssumptions(std::vector<SatLiteral>& unsat_assumptions) override;

  bool ok() const override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  /** Incremental interface */

  uint32_t getAssertionLevel() const override;

  void push() override;

  void pop() override;

  void resetTrail() override;

  void requirePhase(SatLiteral lit) override;

  bool isDecision(SatVariable decn) const override;

  bool isFixed(SatVariable var) const override;

  /** Return the list of current list of decisions that have been made by the
   * solver at the point when this function is called.
   */
  std::vector<SatLiteral> getDecisions() const override;

  /** Return the order heap.
   */
  std::vector<Node> getOrderHeap() const override;

  /** Retrieve a pointer to the underlying solver. */
  Minisat::SimpSolver* getSolver() { return d_minisat; }

  /** Retrieve the proof manager of this SAT solver. */
  SatProofManager* getProofManager();

  /** Retrieve the refutation proof of this SAT solver. */
  std::shared_ptr<ProofNode> getProof() override;

 private:

  /** The SatSolver used */
  Minisat::SimpSolver* d_minisat;

  /** Context we will be using to synchronize the sat solver */
  context::Context* d_context;

  /**
   * Stores assumptions passed via last solve() call.
   *
   * It is used in getUnsatAssumptions() to determine which of the literals in
   * the final conflict clause are assumptions.
   */
  std::unordered_set<SatLiteral, SatLiteralHashFunction> d_assumptions;

  void setupOptions();

  class Statistics {
  private:
   ReferenceStat<int64_t> d_statStarts, d_statDecisions;
   ReferenceStat<int64_t> d_statRndDecisions, d_statPropagations;
   ReferenceStat<int64_t> d_statConflicts, d_statClausesLiterals;
   ReferenceStat<int64_t> d_statLearntsLiterals, d_statMaxLiterals;
   ReferenceStat<int64_t> d_statTotLiterals;

  public:
   Statistics(StatisticsRegistry& registry);
   void init(Minisat::SimpSolver* d_minisat);
   void deinit();
  };/* class MinisatSatSolver::Statistics */
  Statistics d_statistics;

}; /* class MinisatSatSolver */

}  // namespace prop
}  // namespace cvc5::internal

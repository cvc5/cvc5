/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for CaDiCaL SAT Solver.
 *
 * Implementation of the CaDiCaL SAT solver for cvc5 (bit-vectors).
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__CADICAL_H
#define CVC5__PROP__CADICAL_H

#include <cadical.hpp>

#include "prop/sat_solver.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace prop {

class CadicalPropagator;

class CadicalSolver : public CDCLTSatSolver, protected EnvObj
{
  friend class SatSolverFactory;

 public:
  ~CadicalSolver() override;

  /* SatSolver interface -------------------------------------------------- */

  ClauseId addClause(SatClause& clause, bool removable) override;

  ClauseId addXorClause(SatClause& clause, bool rhs, bool removable) override;

  SatVariable newVar(bool isTheoryAtom = false, bool canErase = true) override;

  SatVariable trueVar() override;

  SatVariable falseVar() override;

  SatValue solve() override;
  SatValue solve(long unsigned int&) override;
  SatValue solve(const std::vector<SatLiteral>& assumptions) override;
  bool setPropagateOnly() override;
  void getUnsatAssumptions(std::vector<SatLiteral>& assumptions) override;

  void interrupt() override;

  SatValue value(SatLiteral l) override;

  SatValue modelValue(SatLiteral l) override;

  uint32_t getAssertionLevel() const override;

  bool ok() const override;

  /* CDCLTSatSolver interface --------------------------------------------- */

  void initialize(context::Context* context,
                  prop::TheoryProxy* theoryProxy,
                  context::UserContext* userContext,
                  ProofNodeManager* pnm) override;
  void push() override;

  void pop() override;

  void resetTrail() override;

  void preferPhase(SatLiteral lit) override;

  bool isDecision(SatVariable var) const override;

  bool isFixed(SatVariable var) const override;

  std::vector<SatLiteral> getDecisions() const override;

  std::vector<Node> getOrderHeap() const override;

  std::shared_ptr<ProofNode> getProof() override;

  SatProofManager* getProofManager() override;

 private:
  /**
   * Constructor.
   * Private to disallow creation outside of SatSolverFactory.
   * Function init() must be called after creation.
   * @param env      The associated environment.
   * @param registry The associated statistics registry.
   * @param name     The name of the SAT solver.
   */
  CadicalSolver(Env& env,
                StatisticsRegistry& registry,
                const std::string& name = "");

  /**
   * Initialize SAT solver instance.
   * Note: Split out to not call virtual functions in constructor.
   */
  void init();

  /**
   * Set resource limit.
   * @param resmgr The associated resource manager.
   */
  void setResourceLimit(ResourceManager* resmgr);

  SatValue _solve(const std::vector<SatLiteral>& assumptions);

  /** The wrapped CaDiCaL instance. */
  std::unique_ptr<CaDiCaL::Solver> d_solver;
  /** The CaDiCaL terminator (for termination via resource manager). */
  std::unique_ptr<CaDiCaL::Terminator> d_terminator;

  /** Context for synchronizing the SAT solver when in CDCL(T) mode. */
  context::Context* d_context = nullptr;
  /** The associated theory proxy (for CDCL(T) mode). */
  prop::TheoryProxy* d_proxy = nullptr;
  /** The CaDiCaL propagator (for CDCL(T) mode). */
  std::unique_ptr<CadicalPropagator> d_propagator;

  /**
   * Stores the current set of assumptions provided via solve() and is used to
   * query the solver if a given assumption is false.
   */
  std::vector<SatLiteral> d_assumptions;

  unsigned d_nextVarIdx;
  bool d_inSatMode;
  /** The variable representing true. */
  SatVariable d_true;
  /** The variable representing false. */
  SatVariable d_false;

  struct Statistics
  {
    IntStat d_numSatCalls;
    IntStat d_numVariables;
    IntStat d_numClauses;
    TimerStat d_solveTime;
    Statistics(StatisticsRegistry& registry, const std::string& prefix);
  };

  Statistics d_statistics;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif  // CVC5__PROP__CADICAL_H

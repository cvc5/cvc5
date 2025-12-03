/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper for CaDiCaL SAT Solver.
 *
 * Implementation of the CaDiCaL SAT solver for cvc5 (bit-vectors).
 */

#include "prop/cadical/cadical.h"

#include <cadical/cadical.hpp>
#include <cadical/tracer.hpp>

#include "base/check.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/proof_options.h"
#include "prop/cadical/cdclt_propagator.h"
#include "prop/cadical/proof_tracer.h"
#include "prop/cadical/util.h"
#include "prop/sat_solver_types.h"
#include "prop/theory_proxy.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"
#include "util/string.h"

namespace cvc5::internal::prop {

using namespace cadical;

/* -------------------------------------------------------------------------- */

class ClauseLearner : public CaDiCaL::Learner
{
 public:
  ClauseLearner(TheoryProxy& proxy, int32_t clause_size)
      : d_proxy(proxy), d_max_clause_size(clause_size)
  {
  }
  ~ClauseLearner() override {}

  bool learning(int size) override
  {
    return d_max_clause_size == 0 || size <= d_max_clause_size;
  }

  void learn(int lit) override
  {
    if (lit)
    {
      SatLiteral slit = toSatLiteral(lit);
      d_clause.push_back(slit);
    }
    else
    {
      d_proxy.notifySatClause(d_clause);
      d_clause.clear();
    }
  }

 private:
  TheoryProxy& d_proxy;
  /** Intermediate literals buffer. */
  std::vector<SatLiteral> d_clause;
  /** Maximum size of clauses to get notified about. */
  int32_t d_max_clause_size;
};

CadicalSolver::CadicalSolver(Env& env,
                             StatisticsRegistry& registry,
                             const std::string& name)
    : EnvObj(env),
      d_solver(new CaDiCaL::Solver()),
      d_context(context()),
      // Note: CaDiCaL variables start with index 1 rather than 0 since negated
      //       literals are represented as the negation of the index.
      d_nextVarIdx(1),
      d_inSatMode(false),
      d_statistics(registry, name)
{
}

void CadicalSolver::init()
{
  d_solver->set("quiet", 1);  // CaDiCaL is verbose by default

  // walk and lucky phase do not use the external propagator, disable for now
  if (d_propagator)
  {
    d_solver->set("walk", 0);
    d_solver->set("lucky", 0);
    // ilb currently does not play well with user propagators
    d_solver->set("ilb", 0);
    d_solver->set("ilbassumptions", 0);
    d_solver->connect_fixed_listener(d_propagator.get());
    d_solver->connect_external_propagator(d_propagator.get());
  }

  d_true = newVar();
  d_false = newVar();
  d_solver->add(toCadicalVar(d_true));
  d_solver->add(0);
  d_solver->add(-toCadicalVar(d_false));
  d_solver->add(0);

  bool logProofs = false;
  // TODO (wishue #154): determine how to initialize the proofs for CaDiCaL
  // here based on d_env.isSatProofProducing and options().proof.propProofMode.
  // The latter should be extended to include modes DRAT and LRAT based on
  // what is available here.
  if (logProofs)
  {
    d_pfFile = options().driver.filename + ".drat_proof.txt";
    if (!options().proof.dratBinaryFormat)
    {
      d_solver->set("binary", 0);
    }
    d_solver->set("inprocessing", 0);
    d_solver->trace_proof(d_pfFile.c_str());
  }
}

CadicalSolver::~CadicalSolver()
{
  if (d_proof_tracer != nullptr)
  {
    d_solver->disconnect_proof_tracer(d_proof_tracer.get());
  }
}

/**
 * Terminator class that notifies CaDiCaL to terminate when the resource limit
 * is reached (used for resource limits specified via --rlimit or --tlimit).
 */
class ResourceLimitTerminator : public CaDiCaL::Terminator
{
 public:
  ResourceLimitTerminator(ResourceManager& resmgr) : d_resmgr(resmgr) {};

  bool terminate() override
  {
    d_resmgr.spendResource(Resource::BvSatStep);
    return d_resmgr.out();
  }

 private:
  ResourceManager& d_resmgr;
};

void CadicalSolver::setResourceLimit(ResourceManager* resmgr)
{
  d_terminator.reset(new ResourceLimitTerminator(*resmgr));
  d_solver->connect_terminator(d_terminator.get());
}

SatValue CadicalSolver::_solve(const std::vector<SatLiteral>& assumptions)
{
  if (d_propagator)
  {
    Trace("cadical::propagator") << "solve start" << std::endl;
    d_propagator->renotify_fixed();
  }
  TimerStat::CodeTimer codeTimer(d_statistics.d_solveTime);
  d_assumptions.clear();
  if (d_propagator)
  {
    // Assume activation literals for all active user levels.
    for (const auto& lit : d_propagator->activation_literals())
    {
      Trace("cadical::propagator")
          << "assume activation lit: " << ~lit << std::endl;
      d_solver->assume(toCadicalLit(~lit));
    }
  }
  SatValue res;
  for (const SatLiteral& lit : assumptions)
  {
    if (d_propagator)
    {
      Trace("cadical::propagator") << "assume: " << lit << std::endl;
    }
    d_solver->assume(toCadicalLit(lit));
    d_assumptions.push_back(lit);
  }
  if (d_propagator)
  {
    d_propagator->in_search(true);
  }
  res = toSatValue(d_solver->solve());
  if (d_propagator)
  {
    Assert(res != SAT_VALUE_TRUE || d_propagator->done());
    Trace("cadical::propagator") << "solve done: " << res << std::endl;
    d_propagator->in_search(false);
  }
#ifndef NDEBUG
  // Check unsat core
  if (res == SAT_VALUE_FALSE && d_proof_tracer != nullptr)
  {
    std::vector<SatClause> unsat_core;
    d_proof_tracer->compute_unsat_core(unsat_core, true);

    std::unique_ptr<CaDiCaL::Solver> solver(new CaDiCaL::Solver());
    for (const auto& clause : unsat_core)
    {
      for (const auto& lit : clause)
      {
        solver->add(toCadicalLit(lit));
      }
      solver->add(0);
    }
    Assert(solver->solve() == CaDiCaL::UNSATISFIABLE);
  }
#endif
  ++d_statistics.d_numSatCalls;
  d_inSatMode = (res == SAT_VALUE_TRUE);
  return res;
}

/* SatSolver Interface ------------------------------------------------------ */

ClauseId CadicalSolver::addClause(SatClause& clause, bool removable)
{
  if (d_propagator && TraceIsOn("cadical::propagator"))
  {
    Trace("cadical::propagator") << "addClause (" << removable << "):";
    SatLiteral alit = d_propagator->current_activation_lit();
    if (alit != undefSatLiteral)
    {
      Trace("cadical::propagator") << " " << alit;
    }
    for (const SatLiteral& lit : clause)
    {
      Trace("cadical::propagator") << " " << lit;
    }
    Trace("cadical::propagator") << " 0" << std::endl;
  }
  if (d_propagator)
  {
    d_propagator->add_clause(clause);
  }
  else
  {
    for (const SatLiteral& lit : clause)
    {
      d_solver->add(toCadicalLit(lit));
    }
    d_solver->add(0);
  }
  ++d_statistics.d_numClauses;
  return ClauseIdError;
}

ClauseId CadicalSolver::addXorClause(SatClause& clause,
                                     bool rhs,
                                     bool removable)
{
  Unreachable() << "CaDiCaL does not support adding XOR clauses.";
  return 0;
}

SatVariable CadicalSolver::newVar(bool isTheoryAtom, bool canErase)
{
  ++d_statistics.d_numVariables;
  if (d_propagator)
  {
    d_propagator->add_new_var(d_nextVarIdx, isTheoryAtom);
  }
  return d_nextVarIdx++;
}

SatVariable CadicalSolver::trueVar() { return d_true; }

SatVariable CadicalSolver::falseVar() { return d_false; }

SatValue CadicalSolver::solve() { return _solve({}); }

SatValue CadicalSolver::solve(long unsigned int&)
{
  Unimplemented() << "Setting limits for CaDiCaL not supported yet";
  return SatValue::SAT_VALUE_UNKNOWN;
};

SatValue CadicalSolver::solve(const std::vector<SatLiteral>& assumptions)
{
  return _solve(assumptions);
}

bool CadicalSolver::setPropagateOnly()
{
  d_solver->limit("decisions", 0); /* Gets reset after next solve() call. */
  return true;
}

void CadicalSolver::getUnsatAssumptions(std::vector<SatLiteral>& assumptions)
{
  for (const SatLiteral& lit : d_assumptions)
  {
    if (d_solver->failed(toCadicalLit(lit)))
    {
      assumptions.push_back(lit);
    }
  }
}

void CadicalSolver::interrupt() { d_solver->terminate(); }

SatValue CadicalSolver::value(SatLiteral l) { return d_propagator->value(l); }

SatValue CadicalSolver::modelValue(SatLiteral l)
{
  Assert(d_inSatMode);
  auto val = d_solver->val(toCadicalLit(l.getSatVariable()));
  return toSatValueLit(l.isNegated() ? -val : val);
}

uint32_t CadicalSolver::getAssertionLevel() const
{
  Assert(d_propagator);
  return d_propagator->current_user_level();
}

bool CadicalSolver::ok() const { return d_inSatMode; }

CadicalSolver::Statistics::Statistics(StatisticsRegistry& registry,
                                      const std::string& prefix)
    : d_numSatCalls(registry.registerInt(prefix + "cadical::calls_to_solve")),
      d_numVariables(registry.registerInt(prefix + "cadical::variables")),
      d_numClauses(registry.registerInt(prefix + "cadical::clauses")),
      d_solveTime(registry.registerTimer(prefix + "cadical::solve_time"))
{
}

/* CDCLTSatSolver Interface ------------------------------------------------- */

void CadicalSolver::initialize(prop::TheoryProxy* theoryProxy,
                               PropPfManager* ppm)
{
  d_proxy = theoryProxy;
  d_propagator.reset(new CadicalPropagator(
      theoryProxy, d_context, *d_solver, statisticsRegistry()));
  if (!d_env.getPlugins().empty())
  {
    d_clause_learner.reset(new ClauseLearner(*theoryProxy, 0));
    d_solver->connect_learner(d_clause_learner.get());
  }

  if (d_env.isSatProofProducing())
  {
    d_proof_tracer.reset(new ProofTracer(*d_propagator));
    d_solver->connect_proof_tracer(d_proof_tracer.get(), true);
  }

  init();
}

void CadicalSolver::push()
{
  d_context->push();  // SAT context for cvc5
  // Push new user level
  d_propagator->user_push();
  // Set new activation literal for pushed user level
  // Note: This happens after the push to ensure that the activation literal's
  // introduction level is the current user level.
  SatVariable alit = newVar(false);
  d_propagator->set_activation_lit(alit);
}

void CadicalSolver::pop()
{
  d_context->pop();  // SAT context for cvc5
  d_propagator->user_pop();
  // CaDiCaL issues notify_backtrack(0) when done, we don't have to call this
  // explicitly here
}

void CadicalSolver::resetTrail()
{
  // Reset SAT context to decision level 0
  d_propagator->notify_backtrack(0);
}

void CadicalSolver::preferPhase(SatLiteral lit)
{
  Trace("cadical::propagator") << "phase: " << lit << std::endl;
  d_propagator->phase(lit);
}

bool CadicalSolver::isDecision(SatVariable var) const
{
  return d_solver->is_decision(toCadicalVar(var));
}

bool CadicalSolver::isFixed(SatVariable var) const
{
  if (d_propagator)
  {
    return d_propagator->is_fixed(var);
  }
  return d_solver->fixed(toCadicalVar(var));
}

std::vector<SatLiteral> CadicalSolver::getDecisions() const
{
  std::vector<SatLiteral> decisions;
  for (SatLiteral lit : d_propagator->get_decisions())
  {
    if (lit != 0)
    {
      decisions.push_back(lit);
    }
  }
  return decisions;
}

std::vector<Node> CadicalSolver::getOrderHeap() const { return {}; }

std::shared_ptr<ProofNode> CadicalSolver::getProof()
{
  if (d_proof_tracer)
  {
    ProofNodeManager* pnm = d_env.getProofNodeManager();
    NodeManager* nm = d_env.getNodeManager();

    std::vector<SatClause> unsat_core;
    d_proof_tracer->compute_unsat_core(unsat_core);

    std::vector<std::shared_ptr<ProofNode>> ps;
    for (const auto& sat_clause : unsat_core)
    {
      NodeBuilder nb(nm, Kind::OR);
      std::vector<Node> lits;
      for (const auto& lit : sat_clause)
      {
        lits.push_back(d_proxy->getNode(lit));
      }
      // Sat clause is sorted by literal id. Ensure that node-level clause is
      // sorted by node ids.
      std::sort(lits.begin(), lits.end());
      for (const auto& lit : lits)
      {
        nb << lit;
      }
      Node n = nb.getNumChildren() == 1 ? nb[0] : nb.constructNode();
      ps.push_back(pnm->mkAssume(n));
    }
    return pnm->mkNode(ProofRule::SAT_REFUTATION, ps, {});
  }
  // NOTE: we could return a DRAT_REFUTATION or LRAT_REFUTATION proof node
  // consisting of a single step, referencing the files for the DIMACS + proof.
  // do not throw an exception, since we test whether the proof is available
  // by comparing it to nullptr.
  return nullptr;
}

/* -------------------------------------------------------------------------- */
}  // namespace cvc5::internal::prop

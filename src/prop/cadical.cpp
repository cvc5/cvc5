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

#include "prop/cadical.h"

#include <deque>

#include "base/check.h"
#include "options/base_options.h"
#include "options/main_options.h"
#include "options/proof_options.h"
#include "prop/theory_proxy.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"
#include "util/string.h"

namespace cvc5::internal {
namespace prop {

/* -------------------------------------------------------------------------- */

using CadicalLit = int;
using CadicalVar = int;

// helper functions
namespace {

SatValue toSatValue(int result)
{
  if (result == 10) return SAT_VALUE_TRUE;
  if (result == 20) return SAT_VALUE_FALSE;
  Assert(result == 0);
  return SAT_VALUE_UNKNOWN;
}

// Note: CaDiCaL returns lit/-lit for true/false. Older versions returned 1/-1.
SatValue toSatValueLit(int value)
{
  if (value > 0) return SAT_VALUE_TRUE;
  Assert(value < 0);
  return SAT_VALUE_FALSE;
}

CadicalLit toCadicalLit(const SatLiteral lit)
{
  return lit.isNegated() ? -lit.getSatVariable() : lit.getSatVariable();
}

SatLiteral toSatLiteral(CadicalLit lit)
{
  return SatLiteral(std::abs(lit), lit < 0);
}

CadicalVar toCadicalVar(SatVariable var) { return var; }

}  // namespace helper functions

class CadicalPropagator : public CaDiCaL::ExternalPropagator
{
 public:
  CadicalPropagator(prop::TheoryProxy* proxy,
                    context::Context* context,
                    CaDiCaL::Solver& solver)
      : d_proxy(proxy), d_context(*context), d_solver(solver)
  {
    d_var_info.emplace_back();  // 0: Not used
  }

  /**
   * Notification from the SAT solver on assignment of a new literal.
   *
   * Saves assignment for notified literal, enqueues corresponding theory
   * literal in theory proxy.
   *
   * @param lit      The CaDiCaL literal that was assigned.
   * @param is_fixed True if the assignment is fixed (on level 0).
   */
  void notify_assignment(int lit, bool is_fixed) override
  {
    if (d_found_solution)
    {
      return;
    }

    SatLiteral slit = toSatLiteral(lit);
    SatVariable var = slit.getSatVariable();
    Assert(var < d_var_info.size());

    auto& info = d_var_info[var];

    // Only consider active variables
    if (!info.is_active)
    {
      return;
    }

    bool is_decision = d_solver.is_decision(lit);

    Trace("cadical::propagator")
        << "notif::assignment: [" << (is_decision ? "d" : "p") << "] " << slit
        << " (fixed: " << is_fixed << ", level: " << d_decisions.size()
        << ", level_intro: " << info.level_intro
        << ", level_user: " << current_user_level() << ")" << std::endl;

    // Save decision variables
    if (is_decision)
    {
      d_decisions.back() = slit;
    }

    Assert(info.assignment == 0 || info.assignment == lit);
    Assert(info.assignment == 0 || is_fixed);

    // Assignment of literal is fixed
    if (is_fixed)
    {
      Assert(!info.is_fixed);
      info.is_fixed = true;
      info.level_fixed = current_user_level();
    }

    // Only notify theory proxy if variable was assigned a new value, not if it
    // got fixed after assignment already happend.
    if (info.assignment == 0)
    {
      info.assignment = lit;
      d_assignments.push_back(slit);
      if (info.is_theory_atom)
      {
        Trace("cadical::propagator") << "enqueue: " << slit << std::endl;
        Trace("cadical::propagator")
            << "node:    " << d_proxy->getNode(slit) << std::endl;
        d_proxy->enqueueTheoryLiteral(slit);
      }
    }
  }

  /**
   * Notification from the SAT solver when it makes a decision.
   * Pushes new SAT context level.
   */
  void notify_new_decision_level() override
  {
    d_context.push();
    d_assignment_control.push_back(d_assignments.size());
    d_decisions.emplace_back();
    Trace("cadical::propagator")
        << "notif::decision: new level " << d_decisions.size() << std::endl;
  }

  /**
   * Notification from the SAT solver on backtrack to the given level.
   *
   * This will automatically backtrack decisions and assignments to the
   * specified level. Fixed assignments that get backtracked will be
   * re-assigned at `level` and the corresponding theory literals are
   * re-enqueued in the theory proxy.
   *
   * @param level The level the SAT solver backtracked to.
   */
  void notify_backtrack(size_t level) override
  {
    Trace("cadical::propagator") << "notif::backtrack: " << level << std::endl;

    // CaDiCaL may notify us about backtracks of decisions that we were not
    // notified about. We can safely ignore them.
    if (d_decisions.size() <= level)
    {
      Assert(d_decisions.size() == 0);
      return;
    }
    d_found_solution = false;

    // Backtrack decisions
    Assert(d_decisions.size() > level);
    Assert(d_context.getLevel() > level);
    for (size_t cur_level = d_decisions.size(); cur_level > level; --cur_level)
    {
      d_context.pop();
      d_decisions.pop_back();
    }

    // Backtrack assignments, resend fixed theory literals that got backtracked
    Assert(!d_assignment_control.empty());
    size_t pop_to = d_assignment_control[level];
    d_assignment_control.resize(level);

    std::vector<SatLiteral> fixed;
    while (pop_to < d_assignments.size())
    {
      SatLiteral lit = d_assignments.back();
      d_assignments.pop_back();
      SatVariable var = lit.getSatVariable();
      auto& info = d_var_info[var];
      if (info.is_fixed)
      {
        if (info.is_theory_atom)
        {
          Assert(info.is_active);
          fixed.push_back(lit);
        }
      }
      else
      {
        Trace("cadical::propagator") << "unassign: " << var << std::endl;
        info.assignment = 0;
      }
    }

    // Notify theory proxy about backtrack
    d_proxy->notifyBacktrack();
    // Clear the propgations since they are not valid anymore.
    d_propagations.clear();

    // Re-enqueue fixed theory literals that got removed. Re-enqueue in the
    // order they got assigned in, i.e., reverse order on vector `fixed`.
    for (auto it = fixed.rbegin(), end = fixed.rend(); it != end; ++it)
    {
      SatLiteral lit = *it;
      Trace("cadical::propagator") << "re-enqueue: " << lit << std::endl;
      d_proxy->enqueueTheoryLiteral(lit);
      d_assignments.push_back(lit);
    }
    Trace("cadical::propagator") << "notif::backtrack end" << std::endl;
  }

  /**
   * Callback of the SAT solver on finding a full sat assignment.
   *
   * Checks whether current model is consistent with the theories, performs a
   * full effort check and theory propgations.
   *
   * @param model The full assignment.
   * @return true If the current model is not in conflict with the theories.
   */
  bool cb_check_found_model(const std::vector<int>& model) override
  {
    Trace("cadical::propagator") << "cb::check_found_model" << std::endl;
    bool recheck = false;

    if (d_found_solution)
    {
      return true;
    }
    // CaDiCaL may backtrack while importing clauses, which can result in some
    // clauses not being processed. Make sure to add all clauses before
    // checking the model.
    if (!d_new_clauses.empty())
    {
      Trace("cadical::propagator") << "cb::check_found_model end: new "
                                      "variables added via theory decision"
                                   << std::endl;
      // CaDiCaL expects us to be able to provide a reason for rejecting the
      // model (it asserts that after this call, cb_has_external_clause()
      // returns true). However, in this particular case, we want to force
      // CaDiCaL to give us model values for the new variables that were
      // introduced (to kick off the assignment notification machinery), we
      // don't have a reason clause for rejecting the model. CaDiCaL's
      // expectation will be weakened in the future to allow for this, but for
      // now we simply add a tautology as reason to pacify CaDiCaL.
      d_new_clauses.push_back(1);
      d_new_clauses.push_back(-1);
      d_new_clauses.push_back(0);
      return false;
    }

    // Check full model.
    //
    // First, we have to ensure that if the SAT solver determines sat without
    // making any decisions, theory decisions are still requested until fixed
    // point at least once since some modules, e.g., finite model finding, rely
    // on this. Theory decisions may add new variables (while decisions
    // requested by the decision engine will not). If new variables are added,
    // we interrupt the check to force the SAT solver to extend the model with
    // the new variables.
    size_t size = d_var_info.size();
    bool requirePhase, stopSearch;
    d_proxy->getNextDecisionRequest(requirePhase, stopSearch);
    if (d_var_info.size() != size)
    {
      return false;
    }
    // Theory engine may trigger a recheck, unless new variables were added
    // during check. If so, we break out of the check and have the SAT solver
    // extend the model with the new variables.
    do
    {
      Trace("cadical::propagator")
          << "full check (recheck: " << recheck << ")" << std::endl;
      d_proxy->theoryCheck(theory::Theory::Effort::EFFORT_FULL);
      theory_propagate();
      for (const SatLiteral& p : d_propagations)
      {
        Trace("cadical::propagator")
            << "add propagation reason: " << p << std::endl;
        SatClause clause;
        d_proxy->explainPropagation(p, clause);
        add_clause(clause);
      }
      d_propagations.clear();

      if (!d_new_clauses.empty())
      {
        // Will again call cb_check_found_model() after clauses were added.
        recheck = false;
      }
      else
      {
        recheck = d_proxy->theoryNeedCheck();
      }
    } while (d_var_info.size() == size && recheck);

    if (d_var_info.size() != size)
    {
      Trace("cadical::propagator") << "cb::check_found_model end: new "
                                      "variables added via theory check"
                                   << std::endl;
      // Same as above, until CaDiCaL's assertion that we have to have
      // a reason clause for rejecting the model is weakened, we need to
      // pacify it with a tautology.
      d_new_clauses.push_back(1);
      d_new_clauses.push_back(-1);
      d_new_clauses.push_back(0);
      return false;
    }
    bool res = done();
    Trace("cadical::propagator")
        << "cb::check_found_model end: done: " << res << std::endl;
    return res;
  }

  /**
   * Callback of the SAT solver before making a new decision.
   *
   * Processes decision requests from the theory proxy.
   *
   * @note This may call cb_check_found_model() in case the decision engine
   *       determines that we have a partial model, i.e., stopSearch is true.
   *
   * @return The next decision.
   */
  int cb_decide() override
  {
    if (d_found_solution)
    {
      return 0;
    }
    bool stopSearch = false;
    bool requirePhase = false;
    SatLiteral lit = d_proxy->getNextDecisionRequest(requirePhase, stopSearch);
    // We found a partial model, let's check it.
    if (stopSearch)
    {
      d_found_solution = cb_check_found_model({});
      if (d_found_solution)
      {
        Trace("cadical::propagator") << "Found solution" << std::endl;
        d_found_solution = d_proxy->isDecisionEngineDone();
        if (!d_found_solution)
        {
          Trace("cadical::propagator")
              << "Decision engine not done" << std::endl;
          lit = d_proxy->getNextDecisionRequest(requirePhase, stopSearch);
        }
      }
      else
      {
        Trace("cadical::propagator") << "No solution found yet" << std::endl;
      }
    }
    if (!stopSearch && lit != undefSatLiteral)
    {
      if (!requirePhase)
      {
        int8_t phase = d_var_info[lit.getSatVariable()].phase;
        if (phase != 0)
        {
          if ((phase == -1 && !lit.isNegated())
              || (phase == 1 && lit.isNegated()))
          {
            lit = ~lit;
          }
        }
      }
      Trace("cadical::propagator") << "cb::decide: " << lit << std::endl;
      return toCadicalLit(lit);
    }
    Trace("cadical::propagator") << "cb::decide: 0" << std::endl;
    return 0;
  }

  /**
   * Callback of the SAT solver after BCP.
   *
   * Performs standard theory check and theory propagations.
   *
   * If we don't have any theory propagations queued in d_propagations, we
   * perform an EFFORT_STANDARD check in combination with theory_propagate() to
   * populate d_propagations.
   *
   * @return The next theory propagation.
   */
  int cb_propagate() override
  {
    if (d_found_solution)
    {
      return 0;
    }
    Trace("cadical::propagator") << "cb::propagate" << std::endl;
    if (d_propagations.empty())
    {
      // Only propagate if all activation literals are processed. Activation
      // literals are always assumed first. If we don't do this, explanations
      // for theory propgations may force activation literals to different
      // values before they can get decided on.
      if (d_decisions.size() < current_user_level())
      {
        return 0;
      }
      d_proxy->theoryCheck(theory::Theory::Effort::EFFORT_STANDARD);
      theory_propagate();
    }
    return next_propagation();
  }

  /**
   * Callback of the SAT solver asking for the explanation of a theory literal.
   * @note This is called on `propagated_lit` until the reason clause is
   *       fully processed.
   * @param propagated_lit The theory literal.
   * @return The next literal of the reason clause, 0 to terminate the clause.
   */
  int cb_add_reason_clause_lit(int propagated_lit) override
  {
    // Get reason for propagated_lit.
    if (!d_processing_reason)
    {
      Assert(d_reason.empty());
      SatLiteral slit = toSatLiteral(propagated_lit);
      SatClause clause;
      d_proxy->explainPropagation(slit, clause);
      // Add activation literal to reason
      SatLiteral alit = current_activation_lit();
      if (alit != undefSatLiteral)
      {
        d_reason.push_back(alit);
      }
      d_reason.insert(d_reason.end(), clause.begin(), clause.end());
      d_processing_reason = true;
      Trace("cadical::propagator")
          << "cb::reason: " << slit << ", size: " << d_reason.size()
          << std::endl;
    }

    // We are done processing the reason for propagated_lit.
    if (d_reason.empty())
    {
      d_processing_reason = false;
      return 0;
    }

    // Return next literal of the reason for propagated_lit.
    Trace("cadical::propagator")
        << "cb::reason: " << toSatLiteral(propagated_lit) << " "
        << d_reason.front() << std::endl;
    int lit = toCadicalLit(d_reason.front());
    d_reason.pop_front();
    return lit;
  }

  /**
   * Callback of the SAT solver to determine if we have a new clause to add.
   * @return True to indicate that we have clauses to add.
   */
  bool cb_has_external_clause() override { return !d_new_clauses.empty(); }

  /**
   * Callback of the SAT solver to add a new clause.
   * @note This is called consecutively until the full clause is processed.
   * @note Clauses are terminated with 0 in d_new_clauses.
   * @return The next literal of the clause, 0 to terminate the clause.
   */
  int cb_add_external_clause_lit() override
  {
    Assert(!d_new_clauses.empty());
    CadicalLit lit = d_new_clauses.front();
    d_new_clauses.pop_front();
    Trace("cadical::propagator")
        << "external_clause: " << toSatLiteral(lit) << std::endl;
    return lit;
  }

  /**
   * Get the current trail of decisions.
   * @return The trail of decisions.
   */
  const std::vector<SatLiteral>& get_decisions() const { return d_decisions; }

  /**
   * Get the current assignment of lit.
   *
   * Note: This does not query d_solver->val() since this can only be queried
   * if the SAT solver is in a SAT state, which is not the case during solving.
   *
   * @param lit SatLiteral to be queried.
   * @return Current value of given literal on the trail.
   */
  SatValue value(SatLiteral lit) const
  {
    SatVariable var = lit.getSatVariable();
    SatValue val = SAT_VALUE_UNKNOWN;
    int32_t assign = d_var_info[var].assignment;
    if (assign != 0)
    {
      val = toSatValueLit(lit.isNegated() ? -assign : assign);
    }
    Trace("cadical::propagator")
        << "value: " << lit << ": " << val << std::endl;
    return val;
  }

  /**
   * Adds a new clause to the propagator.
   *
   * The clause will not immediately added to the SAT solver, but instead
   * will be added through the `cb_add_external_clause_lit` callback.
   *
   * Note: Filters out clauses satisfied by fixed literals.
   *
   * @param clause The clause to add.
   */
  void add_clause(const SatClause& clause)
  {
    std::vector<CadicalLit> lits;
    for (const SatLiteral& lit : clause)
    {
      SatVariable var = lit.getSatVariable();
      Assert(var < d_var_info.size());
      const auto& info = d_var_info[var];
      Assert(info.is_active);
      if (info.is_fixed)
      {
        int32_t val = lit.isNegated() ? -info.assignment : info.assignment;
        Assert(val != 0);
        if (val > 0)
        {
          // Clause satisfied by fixed literal, no clause added
          return;
        }
      }
      lits.push_back(toCadicalLit(lit));
    }
    if (!lits.empty())
    {
      // Add activation literal to clause if we are in user level > 0
      SatLiteral alit = current_activation_lit();
      if (alit != undefSatLiteral)
      {
        lits.insert(lits.begin(), toCadicalLit(alit));
      }
      // Do not immediately add clauses added during search. We have to buffer
      // them and add them during the cb_add_reason_clause_lit callback.
      if (d_in_search)
      {
        d_new_clauses.insert(d_new_clauses.end(), lits.begin(), lits.end());
        d_new_clauses.push_back(0);
      }
      else
      {
        for (const auto& lit : lits)
        {
          d_solver.add(lit);
        }
        d_solver.add(0);
      }
    }
  }

  /**
   * Add new CaDiCaL variable.
   * @param var            The variable to add.
   * @param level          The current user assertion level.
   * @param is_theory_atom True if variable is a theory atom.
   * @param in_search      True if SAT solver is currently in search().
   */
  void add_new_var(const SatVariable& var, bool is_theory_atom)
  {
    // Since activation literals are not tracked here, we have to make sure to
    // properly resize d_var_info.
    if (var > d_var_info.size())
    {
      d_var_info.resize(var);
    }
    Assert(d_var_info.size() == var);

    // Boolean variables are not theory atoms, but may still occur in
    // lemmas/conflicts sent to the SAT solver. Hence, we have to observe them
    // since CaDiCaL expects all literals sent back to be observed.
    d_solver.add_observed_var(toCadicalVar(var));
    d_active_vars.push_back(var);
    Trace("cadical::propagator")
        << "new var: " << var << " (level: " << current_user_level()
        << ", is_theory_atom: " << is_theory_atom
        << ", in_search: " << d_in_search << ")" << std::endl;
    auto& info = d_var_info.emplace_back();
    info.level_intro = current_user_level();
    info.is_theory_atom = is_theory_atom;
  }

  /**
   * Checks whether the theory engine is done, no new clauses need to be added
   * and the current model is consistent.
   */
  bool done() const
  {
    if (!d_new_clauses.empty())
    {
      Trace("cadical::propagator") << "not done: pending clauses" << std::endl;
      return false;
    }
    if (d_proxy->theoryNeedCheck())
    {
      Trace("cadical::propagator")
          << "not done: theory need check" << std::endl;
      return false;
    }
    if (d_found_solution)
    {
      Trace("cadical::propagator")
          << "done: found partial solution" << std::endl;
    }
    else
    {
      Trace("cadical::propagator")
          << "done: full assignment consistent" << std::endl;
    }
    return true;
  }

  /**
   * Push user assertion level.
   */
  void user_push()
  {
    Trace("cadical::propagator")
        << "user push: " << d_active_vars_control.size();
    d_active_vars_control.push_back(d_active_vars.size());
    Trace("cadical::propagator")
        << " -> " << d_active_vars_control.size() << std::endl;
  }

  /**
   * Set the activation literal for the current user assertion level.
   *
   * @param alit The activation literal for the current user assertion level.
   */
  void set_activation_lit(SatVariable& alit)
  {
    d_activation_literals.push_back(alit);
    Trace("cadical::propagator")
      << "enable activation lit: " << alit << std::endl;
  }

  /**
   * Pop user assertion level.
   */
  void user_pop()
  {
    Trace("cadical::propagator")
        << "user pop: " << d_active_vars_control.size();
    size_t pop_to = d_active_vars_control.back();
    d_active_vars_control.pop_back();
    Trace("cadical::propagator")
        << " -> " << d_active_vars_control.size() << std::endl;

    // Disable activation literal for popped user level. The activation literal
    // is added as unit clause, which will satisfy all clauses added in this
    // user level and get garbage collected in the SAT solver.
    SatLiteral alit = current_activation_lit();
    Trace("cadical::propagator")
        << "disable activation lit: " << alit << std::endl;
    d_activation_literals.pop_back();

    size_t user_level = current_user_level();

    // Unregister popped variables so that CaDiCaL does not notify us anymore
    // about assignments.
    Assert(pop_to <= d_active_vars.size());
    std::vector<SatVariable> fixed;
    while (d_active_vars.size() > pop_to)
    {
      SatVariable var = d_active_vars.back();
      const auto& info = d_var_info[var];
      d_active_vars.pop_back();

      // We keep fixed literals that correspond to theory atoms introduced in
      // lower user levels, since we have to renotify them before the next
      // solve call.
      if (info.is_fixed && info.is_theory_atom
          && info.level_intro <= user_level)
      {
        fixed.push_back(var);
      }
      else
      {
        Trace("cadical::propagator") << "set inactive: " << var << std::endl;
        d_var_info[var].is_active = false;
        d_solver.remove_observed_var(toCadicalVar(var));
        Assert(info.level_intro > user_level);
        // Fix value of inactive variables in order to avoid CaDiCaL from
        // deciding on them again. This make a huge difference in performance
        // for incremental problems with many check-sat calls.
        d_solver.add(toCadicalLit(var));
        d_solver.add(0);
      }
    }
    // Re-add fixed active vars in the order they were added to d_active_vars.
    d_active_vars.insert(d_active_vars.end(), fixed.rbegin(), fixed.rend());

    // We are at decicion level 0 at this point.
    Assert(d_decisions.empty());
    Assert(d_assignment_control.empty());
    // At this point, only fixed literals will be on d_assignments, now we have
    // to determine which of these are still relevant in the current user
    // level. If the variable is still active here, it means that it is still
    // relevant for the current user level. If its assignment was fixed in a
    // higher user level, we have to renotify the fixed literal in the current
    // level (or in the user level of the next solve call). This happens by
    // pushing the literal onto the d_renotify_fixed vector.
    auto it = d_assignments.begin();
    while (it != d_assignments.end())
    {
      SatLiteral lit = *it;
      auto& info = d_var_info[lit.getSatVariable()];
      Assert(info.is_fixed);

      // Remove inactive variables from the assignment vector.
      if (!info.is_active)
      {
        it = d_assignments.erase(it);
        continue;
      }

      // Renotify fixed literals if it was fixed in a higher user level.
      if (info.is_theory_atom && info.level_fixed > user_level)
      {
        Trace("cadical::propagator")
            << "queue renotify: " << lit
            << " (level_intro: " << info.level_intro
            << ", level_fixed: " << info.level_fixed << ")" << std::endl;
        d_renotify_fixed.push_back(lit);
      }
      ++it;
    }
  }

  bool is_fixed(SatVariable var) const { return d_var_info[var].is_fixed; }

  /**
   * Configure and record preferred phase of variable.
   * @param lit The literal.
   */
  void phase(SatLiteral lit)
  {
    d_solver.phase(toCadicalLit(lit));
    d_var_info[lit.getSatVariable()].phase = lit.isNegated() ? -1 : 1;
  }

  /**
   * Return the activation literal for the current user level.
   *
   * Note: Returns undefSatLiteral at user level 0.
   */
  const SatLiteral& current_activation_lit()
  {
    if (d_activation_literals.empty())
    {
      return undefSatLiteral;
    }
    return d_activation_literals.back();
  }

  /** Return the current user (assertion) level. */
  size_t current_user_level() const { return d_active_vars_control.size(); }

  /** Return the current list of activation literals. */
  const std::vector<SatLiteral>& activation_literals()
  {
    return d_activation_literals;
  }

  /**
   * Renotify fixed literals in the current user level.
   *
   * This is done prior to a new solve() call and ensures that fixed literals
   * are enqueued in the theory proxy. This is needed since the SAT solver does
   * not re-notify us about fixed literals.
   */
  void renotify_fixed()
  {
    for (const auto& lit : d_renotify_fixed)
    {
      Trace("cadical::propagator")
          << "re-enqueue (user pop): " << lit << std::endl;
      // Make sure to pre-register the re-enqueued theory literal
      d_proxy->notifySatLiteral(d_proxy->getNode(lit));
      // Re-enqueue fixed theory literal
      d_proxy->enqueueTheoryLiteral(lit);
      // We are notifying fixed literals at the current user level, update the
      // level at which the variable was fixed, so that it will be renotified,
      // if needed in lower user levels.
      d_var_info[lit.getSatVariable()].level_fixed = current_user_level();
    }
    d_renotify_fixed.clear();
  }

  /** Set d_in_search flag to indicate whether solver is currently in search. */
  void in_search(bool flag) { d_in_search = flag; }

 private:
  /** Retrieve theory propagations and add them to the propagations list. */
  void theory_propagate()
  {
    SatClause propagated_lits;
    d_proxy->theoryPropagate(propagated_lits);
    Trace("cadical::propagator")
        << "new propagations: " << propagated_lits.size() << std::endl;

    for (const auto& lit : propagated_lits)
    {
      Trace("cadical::propagator") << "new propagation: " << lit << std::endl;
      d_propagations.push_back(lit);
    }
  }

  /**
   * Get next propagation.
   *
   * @return Return next propagation queued in d_propagations.
   */
  int next_propagation()
  {
    if (d_propagations.empty())
    {
      return 0;
    }
    SatLiteral next = d_propagations.front();
    d_propagations.pop_front();
    Trace("cadical::propagator") << "propagate: " << next << std::endl;
    return toCadicalLit(next);
  }

  /** The associated theory proxy. */
  prop::TheoryProxy* d_proxy = nullptr;

  /** The SAT context. */
  context::Context& d_context;
  CaDiCaL::Solver& d_solver;

  /** Struct to store information on variables. */
  struct VarInfo
  {
    uint32_t level_intro = 0;     // user level at which variable was created
    uint32_t level_fixed = 0;     // user level at which variable was fixed
    bool is_theory_atom = false;  // is variable a theory atom
    bool is_fixed = false;        // has variable fixed assignment
    bool is_active = true;        // is variable active
    int32_t assignment = 0;       // current variable assignment
    int8_t phase = 0;             // preferred phase
  };
  /** Maps SatVariable to corresponding info struct. */
  std::vector<VarInfo> d_var_info;

  /**
   * Currently active variables, can get inactive on user pops.
   * Dependent on user context.
   */
  std::vector<SatVariable> d_active_vars;
  /**
   * Control stack to mananage d_active_vars on user pop.
   *
   * Note: We do not use a User-context-dependent CDList here, since we neeed
   *       to know which variables are popped and thus become inactive.
   */
  std::vector<size_t> d_active_vars_control;

  /**
   * Current activation literals.
   *
   * For each user level, we push a fresh activation literal to the vector (in
   * user_pop()). Activation literals get removed and disabled in user_pop().
   * The size of the vector corresponds to the current user level.
   *
   * The activation literals corrsponding to the current user level gets
   * automtically added to each clause added in this user level. With
   * activation literals we can simulate push/pop of clauses in the SAT solver.
   */
  std::vector<SatLiteral> d_activation_literals;

  /** List of fixed literals to be re-notified in lower user level. */
  std::vector<SatLiteral> d_renotify_fixed;

  /**
   * Variable assignment notifications.
   *
   * Used to unassign variables on backtrack.
   */
  std::vector<SatLiteral> d_assignments;
  /**
   * Control stack to manage d_assignments when backtracking on SAT level.
   *
   * Note: We do not use a SAT-context-depenent CDList for d_assignments, since
   *       we need to know which non-fixed variables are unassigned on
   *       backtrack.
   */
  std::vector<size_t> d_assignment_control;

  /**
   * Stores all observed decision variables.
   *
   * Note: May contain undefSatLiteral for unobserved decision variables.
   */
  std::vector<SatLiteral> d_decisions;

  /** Used by cb_propagate() to return propagated literals. */
  std::deque<SatLiteral> d_propagations;

  /**
   * Used by add_clause() to buffer added clauses, which will be added via
   * cb_add_reason_clause_lit().
   */
  std::deque<CadicalLit> d_new_clauses;

  /**
   * Flag indicating whether cb_add_reason_clause_lit() is currently
   * processing a reason.
   */
  bool d_processing_reason = false;
  /** Reason storage to process current reason in cb_add_reason_clause_lit(). */
  std::deque<SatLiteral> d_reason;

  bool d_found_solution = false;

  /** Flag indicating if SAT solver is in search(). */
  bool d_in_search = false;
};

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

CadicalSolver::~CadicalSolver() {}

/**
 * Terminator class that notifies CaDiCaL to terminate when the resource limit
 * is reached (used for resource limits specified via --rlimit or --tlimit).
 */
class ResourceLimitTerminator : public CaDiCaL::Terminator
{
 public:
  ResourceLimitTerminator(ResourceManager& resmgr) : d_resmgr(resmgr){};

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
  // If we are currently in search, add clauses through the propagator.
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
  return toSatValueLit(d_solver->val(toCadicalLit(l)));
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
  d_propagator.reset(new CadicalPropagator(theoryProxy, d_context, *d_solver));
  if (!d_env.getPlugins().empty())
  {
    d_clause_learner.reset(new ClauseLearner(*theoryProxy, 0));
    d_solver->connect_learner(d_clause_learner.get());
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
  // NOTE: we could return a DRAT_REFUTATION or LRAT_REFUTATION proof node
  // consisting of a single step, referencing the files for the DIMACS + proof.
  // do not throw an exception, since we test whether the proof is available
  // by comparing it to nullptr.
  return nullptr;
}

/* -------------------------------------------------------------------------- */
}  // namespace prop
}  // namespace cvc5::internal

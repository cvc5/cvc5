/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * CDCL(T) IPASIRUP propagator for CaDiCaL.
 */
#include "prop/cadical/cdclt_propagator.h"

namespace cvc5::internal::prop::cadical {

CadicalPropagator::CadicalPropagator(prop::TheoryProxy* proxy,
                                     context::Context* context,
                                     CaDiCaL::Solver& solver,
                                     StatisticsRegistry& stats)
    : d_proxy(proxy), d_context(*context), d_solver(solver), d_stats(stats)
{
  d_var_info.emplace_back();  // 0: Not used
}

void CadicalPropagator::notify_assignment(const std::vector<int>& lits)
{
  if (Trace("cadical::propagator").isConnected())
  {
    Trace("cadical::propagator") << "notif::assignments: { ";
    for (auto lit : lits)
    {
      Trace("cadical::propagator") << lit << " ";
    }
    Trace("cadical::propagator") << "}" << std::endl;
  }
  ++d_stats.notifyAssignment;

  if (d_found_solution)
  {
    return;
  }

  for (const auto& lit : lits)
  {
    SatLiteral slit = toSatLiteral(lit);
    SatVariable var = slit.getSatVariable();
    Assert(var < d_var_info.size());

    auto& info = d_var_info[var];

    // Only consider active variables
    if (!info.is_active)
    {
      continue;
    }

    bool is_decision = d_solver.is_decision(lit);

    Trace("cadical::propagator")
        << "notif::assignment: [" << (is_decision ? "d" : "p") << "] " << slit
        << " (level: " << d_decisions.size()
        << ", level_intro: " << info.level_intro
        << ", level_user: " << current_user_level() << ")" << std::endl;

    // Save decision variables
    if (is_decision)
    {
      d_decisions.back() = slit;
    }

    Assert(info.assignment == 0 || info.assignment == lit);

    // Only notify theory proxy if variable was assigned a new value, not if
    // it got fixed after assignment already happend.
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
}

void CadicalPropagator::notify_fixed_assignment(int lit)
{
  SatLiteral slit = toSatLiteral(lit);
  SatVariable var = slit.getSatVariable();

  // We don't care about non-observed variables
  if (var >= d_var_info.size())
  {
    return;
  }

  auto& info = d_var_info[var];
  // Only consider active variables
  if (!info.is_active)
  {
    return;
  }
  ++d_stats.notifyFixedAssignment;

  Trace("cadical::propagator")
      << "notif::fixed assignment: " << slit << std::endl;

  // Mark as fixed.
  Assert(!info.is_fixed);
  info.is_fixed = true;
  info.level_fixed = current_user_level();
  // Trigger actual assignment.
  notify_assignment({lit});
}

void CadicalPropagator::notify_new_decision_level()
{
  d_context.push();
  d_assignment_control.push_back(d_assignments.size());
  d_decisions.emplace_back();
  Trace("cadical::propagator")
      << "notif::decision: new level " << d_decisions.size() << std::endl;
  ++d_stats.notifyNewDecision;
}

void CadicalPropagator::notify_backtrack(size_t level)
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

  while (pop_to < d_assignments.size())
  {
    SatLiteral lit = d_assignments.back();
    d_assignments.pop_back();
    SatVariable var = lit.getSatVariable();
    auto& info = d_var_info[var];
    Trace("cadical::propagator") << "unassign: " << var << std::endl;
    info.assignment = 0;
  }

  // Notify theory proxy about backtrack
  d_proxy->notifyBacktrack();
  // Clear the propgations since they are not valid anymore.
  d_propagations.clear();
  ++d_stats.notifyBacktrack;

  Trace("cadical::propagator") << "notif::backtrack end" << std::endl;
}

bool CadicalPropagator::cb_check_found_model(const std::vector<int>& model)
{
  Trace("cadical::propagator") << "cb::check_found_model" << std::endl;
  bool recheck = false;

  if (d_found_solution)
  {
    return true;
  }

  ++d_stats.cbCheckFoundModel;
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
    Trace("cadical::propagator") << "cb::check_found_model end: new "
                                    "variables added via theory decision"
                                 << std::endl;
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

int CadicalPropagator::cb_decide()
{
  Trace("cadical::propagator") << "cb::decide" << std::endl;
  if (d_found_solution)
  {
    return 0;
  }
  ++d_stats.cbDecide;
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
        Trace("cadical::propagator") << "Decision engine not done" << std::endl;
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

int CadicalPropagator::cb_propagate()
{
  if (d_found_solution)
  {
    return 0;
  }
  ++d_stats.cbPropagate;
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

int CadicalPropagator::cb_add_reason_clause_lit(int propagated_lit)
{
  ++d_stats.cbAddReasonClauseLit;
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
        << "cb::reason: " << slit << ", size: " << d_reason.size() << std::endl;
  }

  // We are done processing the reason for propagated_lit.
  if (d_reason.empty())
  {
    d_processing_reason = false;
    return 0;
  }

  // Return next literal of the reason for propagated_lit.
  Trace("cadical::propagator") << "cb::reason: " << toSatLiteral(propagated_lit)
                               << " " << d_reason.front() << std::endl;
  int lit = toCadicalLit(d_reason.front());
  d_reason.pop_front();
  return lit;
}

bool CadicalPropagator::cb_has_external_clause(bool& is_forgettable)
{
  ++d_stats.cbHasExternalClause;
  is_forgettable = false;
  return !d_new_clauses.empty();
}

int CadicalPropagator::cb_add_external_clause_lit()
{
  ++d_stats.cbAddExternalClauseLit;
  Assert(!d_new_clauses.empty());
  CadicalLit lit = d_new_clauses.front();
  d_new_clauses.pop_front();
  Trace("cadical::propagator")
      << "external_clause: " << toSatLiteral(lit) << std::endl;
  return lit;
}

SatValue CadicalPropagator::value(SatLiteral lit) const
{
  SatVariable var = lit.getSatVariable();
  SatValue val = SAT_VALUE_UNKNOWN;
  int32_t assign = d_var_info[var].assignment;
  if (assign != 0)
  {
    val = toSatValueLit(lit.isNegated() ? -assign : assign);
  }
  Trace("cadical::propagator") << "value: " << lit << ": " << val << std::endl;
  return val;
}

void CadicalPropagator::add_clause(const SatClause& clause)
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
  // // Add empty clause
  // else if (num_false == clause.size())
  // {
  //   d_solver.add(0);
  // }
}

void CadicalPropagator::add_new_var(const SatVariable& var, bool is_theory_atom)
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

bool CadicalPropagator::done() const
{
  if (!d_new_clauses.empty())
  {
    Trace("cadical::propagator") << "not done: pending clauses" << std::endl;
    return false;
  }
  if (d_proxy->theoryNeedCheck())
  {
    Trace("cadical::propagator") << "not done: theory need check" << std::endl;
    return false;
  }
  if (d_found_solution)
  {
    Trace("cadical::propagator") << "done: found partial solution" << std::endl;
  }
  else
  {
    Trace("cadical::propagator")
        << "done: full assignment consistent" << std::endl;
  }
  return true;
}

void CadicalPropagator::user_push()
{
  Trace("cadical::propagator") << "user push: " << d_active_vars_control.size();
  d_active_vars_control.push_back(d_active_vars.size());
  Trace("cadical::propagator")
      << " -> " << d_active_vars_control.size() << std::endl;
}

void CadicalPropagator::set_activation_lit(SatVariable& alit)
{
  d_activation_literals.push_back(alit);
  Trace("cadical::propagator")
      << "enable activation lit: " << alit << std::endl;
}

void CadicalPropagator::user_pop()
{
  Trace("cadical::propagator") << "user pop: " << d_active_vars_control.size();
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
    if (info.is_fixed && info.is_theory_atom && info.level_intro <= user_level)
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
          << "queue renotify: " << lit << " (level_intro: " << info.level_intro
          << ", level_fixed: " << info.level_fixed << ")" << std::endl;
      d_renotify_fixed.push_back(lit);
    }
    ++it;
  }
}

void CadicalPropagator::phase(SatLiteral lit)
{
  d_solver.phase(toCadicalLit(lit));
  d_var_info[lit.getSatVariable()].phase = lit.isNegated() ? -1 : 1;
}

const SatLiteral& CadicalPropagator::current_activation_lit()
{
  if (d_activation_literals.empty())
  {
    return undefSatLiteral;
  }
  return d_activation_literals.back();
}

void CadicalPropagator::renotify_fixed()
{
  ++d_stats.renotifyFixed;
  for (const auto& lit : d_renotify_fixed)
  {
    Trace("cadical::propagator")
        << "re-enqueue (user pop): " << lit << std::endl;
    // Re-enqueue fixed theory literal
    d_proxy->enqueueTheoryLiteral(lit);
    // We are notifying fixed literals at the current user level, update the
    // level at which the variable was fixed, so that it will be renotified,
    // if needed in lower user levels.
    d_var_info[lit.getSatVariable()].level_fixed = current_user_level();
    ++d_stats.renotifyFixedLit;
  }
  d_renotify_fixed.clear();
}

void CadicalPropagator::theory_propagate()
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

int CadicalPropagator::next_propagation()
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

}  // namespace cvc5::internal::prop::cadical

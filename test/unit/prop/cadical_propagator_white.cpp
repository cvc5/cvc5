/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::prop::cadical::CadicalPropagator, in particular
 * the user level assigned to clauses added during search.
 */

#include <cadical/cadical.hpp>

#include "context/context.h"
#include "prop/cadical/cdclt_propagator.h"
#include "prop/cadical/util.h"
#include "prop/sat_solver_types.h"
#include "test.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {

using namespace prop;
using namespace prop::cadical;

namespace test {

class TestPropWhiteCadicalPropagator : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_stats.reset(new StatisticsRegistry());
    d_context.reset(new context::Context());
    d_solver.reset(new CaDiCaL::Solver());
    d_prop.reset(
        new CadicalPropagator(nullptr, d_context.get(), *d_solver, *d_stats));
    // Observed variables require a connected external propagator.
    d_solver->connect_external_propagator(d_prop.get());

    // Build three user levels. This mirrors CadicalSolver::push(), which
    // creates the activation literal *after* incrementing the user level, so
    // the activation literal's introduction level is the new user level.
    //
    //   level 0: variables 1, 2
    //   level 1: activation literal 3, variable 4
    //   level 2: activation literal 5, variable 6
    d_prop->add_new_var(1, true);
    d_prop->add_new_var(2, true);

    d_prop->user_push();
    d_prop->add_new_var(3, false);
    d_prop->set_activation_lit(3);
    d_prop->add_new_var(4, true);

    d_prop->user_push();
    d_prop->add_new_var(5, false);
    d_prop->set_activation_lit(5);
    d_prop->add_new_var(6, true);
  }

  void TearDown() override
  {
    d_solver->disconnect_external_propagator();
    d_prop.reset(nullptr);
    d_solver.reset(nullptr);
    d_context.reset(nullptr);
    d_stats.reset(nullptr);
  }

  /**
   * Drain the next clause buffered by add_clause() (during search) via the
   * external-clause callbacks and return its CaDiCaL literals (without the
   * terminating 0).
   */
  std::vector<int> nextClause()
  {
    std::vector<int> clause;
    bool forgettable = true;
    EXPECT_TRUE(d_prop->cb_has_external_clause(forgettable));
    for (int lit = d_prop->cb_add_external_clause_lit(); lit != 0;
         lit = d_prop->cb_add_external_clause_lit())
    {
      clause.push_back(lit);
    }
    return clause;
  }

  std::unique_ptr<StatisticsRegistry> d_stats;
  std::unique_ptr<context::Context> d_context;
  std::unique_ptr<CaDiCaL::Solver> d_solver;
  std::unique_ptr<CadicalPropagator> d_prop;
};

TEST_F(TestPropWhiteCadicalPropagator, activation_lit_indexing)
{
  ASSERT_EQ(d_prop->current_user_level(), 2u);
  // Level 0 (base level) has no activation literal.
  ASSERT_EQ(d_prop->activation_lit(0), undefSatLiteral);
  ASSERT_EQ(d_prop->activation_lit(1), SatLiteral(3));
  ASSERT_EQ(d_prop->activation_lit(2), SatLiteral(5));
  ASSERT_EQ(d_prop->current_activation_lit(), SatLiteral(5));
}

TEST_F(TestPropWhiteCadicalPropagator, learned_clause_uses_max_intro_level)
{
  // A clause learned during search whose highest-level literal was introduced
  // at user level 1 must be guarded by level 1's activation literal (3), not
  // the current level's (5), so it survives popping level 2.
  d_prop->in_search(true);
  SatClause clause{SatLiteral(4)};  // variable 4 was introduced at level 1
  d_prop->add_clause(clause);
  EXPECT_EQ(nextClause(),
            (std::vector<int>{toCadicalLit(SatLiteral(3)),
                              toCadicalLit(SatLiteral(4))}));
}

TEST_F(TestPropWhiteCadicalPropagator, learned_clause_takes_max_over_literals)
{
  // max over several literals: {1 (level 0), 4 (level 1)} -> level 1 -> 3.
  d_prop->in_search(true);
  SatClause clause{SatLiteral(1), SatLiteral(4)};
  d_prop->add_clause(clause);
  EXPECT_EQ(nextClause(),
            (std::vector<int>{toCadicalLit(SatLiteral(3)),
                              toCadicalLit(SatLiteral(1)),
                              toCadicalLit(SatLiteral(4))}));
}

TEST_F(TestPropWhiteCadicalPropagator, learned_clause_over_base_level)
{
  // A clause over only base-level (level 0) literals is globally valid and
  // must not get any activation literal, even at user level 2.
  d_prop->in_search(true);
  SatClause clause{SatLiteral(1), SatLiteral(2)};
  d_prop->add_clause(clause);
  EXPECT_EQ(nextClause(),
            (std::vector<int>{toCadicalLit(SatLiteral(1)),
                              toCadicalLit(SatLiteral(2))}));
}

TEST_F(TestPropWhiteCadicalPropagator, input_clause_uses_current_level)
{
  // Outside search, the clause is guarded by the current user level's
  // activation literal, even if all its literals were introduced at a lower
  // level (the conservative, pre-existing behavior).
  ASSERT_FALSE(d_prop->in_search());
  ASSERT_EQ(d_prop->activation_lit(d_prop->current_user_level()),
            d_prop->current_activation_lit());
}

// The following tests cover the reason path (cb_add_reason_clause_lit()), which
// guards the reason with activation_lit(clause_user_level(reason)). We exercise
// that computation directly rather than driving the callback, since the
// callback obtains the reason via TheoryProxy::explainPropagation() and setting
// up a TheoryProxy requires a full theory engine. explainPropagation() returns
// the propagated literal followed by the negated antecedents, so the reason's
// user level is the max introduction level over all of them.

TEST_F(TestPropWhiteCadicalPropagator, reason_clause_user_level)
{
  // Propagated literal at level 1 with a base-level antecedent: max -> level 1.
  SatClause level1{SatLiteral(4), SatLiteral(1)};
  EXPECT_EQ(d_prop->clause_user_level(level1), 1u);

  // Highest literal at level 2 dominates: max -> level 2.
  SatClause level2{SatLiteral(1), SatLiteral(4), SatLiteral(6)};
  EXPECT_EQ(d_prop->clause_user_level(level2), 2u);

  // Reason derived purely from base-level facts: level 0.
  SatClause base{SatLiteral(1), SatLiteral(2)};
  EXPECT_EQ(d_prop->clause_user_level(base), 0u);
}

TEST_F(TestPropWhiteCadicalPropagator, reason_clause_guard)
{
  // The activation literal cb_add_reason_clause_lit() prepends to the reason is
  // activation_lit(clause_user_level(reason)).

  // A reason depending on level 1 is guarded by level 1's activation literal
  // (3), not the current level's (5), so it survives popping level 2.
  SatClause level1{SatLiteral(4), SatLiteral(1)};
  EXPECT_EQ(d_prop->activation_lit(d_prop->clause_user_level(level1)),
            SatLiteral(3));

  // A reason depending on level 2 is guarded by level 2's activation literal.
  SatClause level2{SatLiteral(6), SatLiteral(4)};
  EXPECT_EQ(d_prop->activation_lit(d_prop->clause_user_level(level2)),
            SatLiteral(5));

  // A reason over only base-level literals is globally valid and gets no
  // activation literal guard.
  SatClause base{SatLiteral(1), SatLiteral(2)};
  EXPECT_EQ(d_prop->activation_lit(d_prop->clause_user_level(base)),
            undefSatLiteral);
}

}  // namespace test
}  // namespace cvc5::internal

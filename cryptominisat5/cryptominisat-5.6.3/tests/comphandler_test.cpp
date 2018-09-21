/******************************************
Copyright (c) 2016, Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "gtest/gtest.h"

#include <set>
using std::set;

#include "src/solver.h"
#include "src/comphandler.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct comp_handle : public ::testing::Test {
    comp_handle()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCompHandler = true;
        //conf.verbosity = 20;
        s = new Solver(&conf, &must_inter);
        s->new_vars(30);
        s->testing_fill_assumptions_set();
        chandle = s->compHandler;
    }
    ~comp_handle()
    {
        delete s;
    }

    Solver* s;
    CompHandler* chandle = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(comp_handle, handle_1_comp)
{
    s->add_clause_outer(str_to_cl("1, -2, 3"));

    chandle->handle();
    EXPECT_TRUE(s->okay());
    EXPECT_EQ(chandle->get_num_vars_removed(), 0u);
}

TEST_F(comp_handle, handle_2_comps)
{
    s->add_clause_outer(str_to_cl("1, -2, 3"));

    s->add_clause_outer(str_to_cl("9, 4, 5"));
    s->add_clause_outer(str_to_cl("5, 6, 7"));

    chandle->handle();
    EXPECT_TRUE(s->okay());
    EXPECT_EQ(chandle->get_num_vars_removed(), 3u);
    EXPECT_EQ(chandle->get_num_components_solved(), 1u);
}

TEST_F(comp_handle, handle_3_comps)
{
    s->add_clause_outer(str_to_cl("1, -2, 3"));

    s->add_clause_outer(str_to_cl("9, 4, 5"));
    s->add_clause_outer(str_to_cl("5, 6, 7"));

    s->add_clause_outer(str_to_cl("19, 14, 15"));
    s->add_clause_outer(str_to_cl("15, 16, 17"));

    chandle->handle();
    EXPECT_TRUE(s->okay());
    EXPECT_EQ(chandle->get_num_components_solved(), 2u);
    EXPECT_EQ(chandle->get_num_vars_removed(), 8u);
}

TEST_F(comp_handle, check_solution_zero_lev_assign)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, 2"));
    s->add_clause_outer(str_to_cl("1, -2"));

    s->add_clause_outer(str_to_cl("11, 12"));
    s->add_clause_outer(str_to_cl("-11, 12"));
    s->add_clause_outer(str_to_cl("11, -12"));

    s->add_clause_outer(str_to_cl("19, 14, 15"));
    s->add_clause_outer(str_to_cl("15, 16, 17"));
    s->add_clause_outer(str_to_cl("17, 16, 18, 14"));
    s->add_clause_outer(str_to_cl("17, 18, 13"));

    chandle->handle();
    EXPECT_TRUE(s->okay());
    EXPECT_EQ(chandle->get_num_components_solved(), 2u);
    EXPECT_EQ(chandle->get_num_vars_removed(), 0u);
    vector<lbool> solution(s->nVarsOuter(), l_Undef);
    chandle->addSavedState(solution);
    check_zero_assigned_lits_contains(s, "1");
    check_zero_assigned_lits_contains(s, "1");
    check_zero_assigned_lits_contains(s, "11");
    check_zero_assigned_lits_contains(s, "12");
}

TEST_F(comp_handle, check_solution_non_zero_lev_assign)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    s->add_clause_outer(str_to_cl("11, 12"));
    s->add_clause_outer(str_to_cl("-11, 12"));

    s->add_clause_outer(str_to_cl("20, 22"));
    s->add_clause_outer(str_to_cl("-24, 22"));

    s->add_clause_outer(str_to_cl("19, 14, 15"));
    s->add_clause_outer(str_to_cl("15, 16, 17"));
    s->add_clause_outer(str_to_cl("17, 16, 18, 14"));
    s->add_clause_outer(str_to_cl("17, 18, 13"));

    chandle->handle();
    EXPECT_TRUE(s->okay());
    EXPECT_EQ(chandle->get_num_components_solved(), 3u);
    EXPECT_EQ(chandle->get_num_vars_removed(), 7u);
    vector<lbool> solution(s->nVarsOuter(), l_Undef);
    chandle->addSavedState(solution);
    EXPECT_TRUE(clause_satisfied("1, 2", solution));
    EXPECT_TRUE(clause_satisfied("-1, 2", solution));
    EXPECT_TRUE(clause_satisfied("11, 12", solution));
    EXPECT_TRUE(clause_satisfied("-11, 12", solution));
    EXPECT_TRUE(clause_satisfied("20, 22", solution));
    EXPECT_TRUE(clause_satisfied("-24, 22", solution));
}

TEST_F(comp_handle, check_unsat)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, 2"));
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, -2"));

    s->add_clause_outer(str_to_cl("19, 14, 15"));
    s->add_clause_outer(str_to_cl("15, 16, 17"));
    s->add_clause_outer(str_to_cl("17, 16, 18, 14"));
    s->add_clause_outer(str_to_cl("17, 18, 13"));

    bool ret = chandle->handle();
    EXPECT_FALSE(ret);
    EXPECT_FALSE(s->okay());
    EXPECT_EQ(chandle->get_num_components_solved(), 1u);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

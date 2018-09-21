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

#include <fstream>

#include "cryptominisat5/cryptominisat.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

void add_clauses_for_simp_check(SATSolver& s)
{
    s.new_vars(4);

    // 1 = 2
    s.add_clause(str_to_cl("1, -2"));
    s.add_clause(str_to_cl("-1, 2"));

    // 3 = 4
    s.add_clause(str_to_cl("3, -4"));
    s.add_clause(str_to_cl("-3, 4"));

    //no elimination
    s.add_clause(str_to_cl("3, 2"));
    s.add_clause(str_to_cl("4, 1"));
}

TEST(stp_test, no_simp_at_startup)
{
    SATSolver s;
    s.set_no_simplify();
    add_clauses_for_simp_check(s);

    s.solve();
    auto eq_xors = s.get_all_binary_xors();
    EXPECT_EQ(eq_xors.size(), 0U);
}

// Needs to be re-written when we can query clauses from the solver
// TEST(stp_test, simp_at_startup)
// {
//     SATSolver s;
//     add_clauses_for_simp_check(s);
//
//     s.solve();
//     auto eq_xors = s.get_all_binary_xors();
//     EXPECT_EQ(eq_xors.size(), 2U);
// }

TEST(stp_test, set_num_threads_true)
{
    SATSolver s;
    s.set_num_threads(5);
    s.new_vars(2);
    s.add_clause(str_to_cl("1,2"));
    s.add_clause(str_to_cl("1,-2"));

    lbool ret = s.solve();
    EXPECT_EQ(ret, l_True);
    EXPECT_EQ(s.get_model()[0], l_True);
}

TEST(stp_test, set_num_threads_false)
{
    SATSolver s;
    s.set_no_simplify_at_startup();
    s.set_num_threads(5);
    s.new_vars(2);
    s.add_clause(str_to_cl("1,2"));
    s.add_clause(str_to_cl("1,-2"));
    s.add_clause(str_to_cl("-1,2"));
    s.add_clause(str_to_cl("-1,-2"));
    lbool ret = s.solve();
    EXPECT_EQ(ret, l_False);
}

TEST(stp_test, default_polar_false)
{
    SATSolver s;
    s.set_no_simplify_at_startup();
    s.set_default_polarity(false);
    s.new_vars(4);
    s.add_clause(str_to_cl("-1, -2, -3, -4"));
    lbool ret = s.solve();
    EXPECT_EQ(ret, l_True);
    for(size_t i = 0; i < 4; i++) {
        EXPECT_EQ(s.get_model()[0], l_False);
    }
}

TEST(stp_test, default_polar_true)
{
    SATSolver s;
    s.set_no_simplify_at_startup();
    s.set_default_polarity(true);
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2, 3, 4"));
    lbool ret = s.solve();
    EXPECT_EQ(ret, l_True);
    for(size_t i = 0; i < 4; i++) {
        EXPECT_EQ(s.get_model()[0], l_True);
    }
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

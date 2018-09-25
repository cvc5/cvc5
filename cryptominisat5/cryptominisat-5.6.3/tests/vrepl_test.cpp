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

#include "src/solver.h"
#include "src/varreplacer.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct varreplace : public ::testing::Test {
    varreplace()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCache = false;
        s = new Solver(&conf, &must_inter);
        s->new_vars(20);
        s->testing_fill_assumptions_set();
        repl = s->varReplacer;
    }
    ~varreplace()
    {
        delete s;
    }
    Solver* s = NULL;
    VarReplacer* repl = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(varreplace, find_one_1)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, -2"));

    s->add_clause_outer(str_to_cl("1, 3, 4, 5"));
    s->add_clause_outer(str_to_cl("2, 3, 4, 5"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);
    EXPECT_EQ(s->get_num_long_irred_cls(), 2);
    check_irred_cls_eq(s, "-2, 3, 4, 5;  2, 3, 4, 5");
}

TEST_F(varreplace, find_one_2)
{
    s->add_clause_outer(str_to_cl("1, -3"));
    s->add_clause_outer(str_to_cl("-1, 3"));

    s->add_clause_outer(str_to_cl("1, 4, 5"));
    s->add_clause_outer(str_to_cl("2, 3, 4, 5"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);
    check_irred_cls_eq(s, "3, 4, 5;  2, 3, 4, 5");
}

TEST_F(varreplace, remove_lit)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    s->add_clause_outer(str_to_cl("1, 2, 5"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);
    check_irred_cls_eq(s, "2, 5");
}

TEST_F(varreplace, remove_cl)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    s->add_clause_outer(str_to_cl("1, -2, 5"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);
    check_irred_cls_eq(s, "");
}

TEST_F(varreplace, replace_twice)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);

    s->add_clause_outer(str_to_cl("3, -2"));
    s->add_clause_outer(str_to_cl("-3, 2"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 2);

    s->add_clause_outer(str_to_cl("1, -2, 3"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 5"));
    check_irred_cls_eq(s, "2, 5");
}

TEST_F(varreplace, replace_thrice)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 1);

    s->add_clause_outer(str_to_cl("3, -2"));
    s->add_clause_outer(str_to_cl("-3, 2"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 2);

    s->add_clause_outer(str_to_cl("4, -2"));
    s->add_clause_outer(str_to_cl("-4, 2"));

    repl->replace_if_enough_is_found();
    EXPECT_EQ(repl->get_num_replaced_vars(), 3);

    s->add_clause_outer(str_to_cl("1, -2, 3"));
    s->add_clause_outer(str_to_cl("1, 2, 4, 5"));
    check_irred_cls_eq(s, "2, 5");
}

TEST_F(varreplace, replace_limit_check_below)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    s->add_clause_outer(str_to_cl("3, -2"));
    s->add_clause_outer(str_to_cl("-3, 2"));

    repl->replace_if_enough_is_found(3);
    EXPECT_EQ(repl->get_num_replaced_vars(), 0);
}

TEST_F(varreplace, replace_limit_check_above)
{
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2"));

    s->add_clause_outer(str_to_cl("3, -2"));
    s->add_clause_outer(str_to_cl("-3, 2"));

    repl->replace_if_enough_is_found(2);
    EXPECT_EQ(repl->get_num_replaced_vars(), 2);
}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

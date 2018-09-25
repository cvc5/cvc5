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
#include "src/compfinder.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct comp_finder : public ::testing::Test {
    comp_finder()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCache = false;
        s = new Solver(&conf, &must_inter);
        s->new_vars(20);
        finder = new CompFinder(s);
    }
    ~comp_finder()
    {
        delete finder;
        delete s;
    }
    CompFinder *finder;
    Solver* s = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(comp_finder, find_1_1)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, -2"));

    finder->find_components();

    EXPECT_EQ(finder->getNumComps(), 1U);
}

TEST_F(comp_finder, find_1_2)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("3, -4, 5"));
    s->add_clause_outer(str_to_cl("7, -5"));
    s->add_clause_outer(str_to_cl("7, 10, 15"));
    s->add_clause_outer(str_to_cl("15, 4, 2"));

    finder->find_components();

    EXPECT_EQ(finder->getNumComps(), 1U);
}

TEST_F(comp_finder, find_2_1)
{
    s->add_clause_outer(str_to_cl("1, 2"));

    s->add_clause_outer(str_to_cl("3, -4, 5"));
    s->add_clause_outer(str_to_cl("7, -5"));
    s->add_clause_outer(str_to_cl("7, 10, 15"));
    s->add_clause_outer(str_to_cl("15, 4"));

    finder->find_components();

    EXPECT_EQ(finder->getNumComps(), 2U);
}

TEST_F(comp_finder, find_2_2)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("1, 14, 17"));

    s->add_clause_outer(str_to_cl("3, -4, 5"));
    s->add_clause_outer(str_to_cl("7, -5"));
    s->add_clause_outer(str_to_cl("7, 10, 15"));
    s->add_clause_outer(str_to_cl("15, 4"));

    finder->find_components();

    EXPECT_EQ(finder->getNumComps(), 2U);
}

TEST_F(comp_finder, find_5_1)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("3, 4, 5"));

    s->add_clause_outer(str_to_cl("6, -7"));
    s->add_clause_outer(str_to_cl("6, -8"));

    s->add_clause_outer(str_to_cl("10, -12, 11"));
    s->add_clause_outer(str_to_cl("10, -17, 9"));

    s->add_clause_outer(str_to_cl("13, -14, 15, -16"));
    s->add_clause_outer(str_to_cl("13, -14, -16"));

    s->add_clause_outer(str_to_cl("-18, -17"));
    s->add_clause_outer(str_to_cl("-18, 20"));

    finder->find_components();

    EXPECT_EQ(finder->getNumComps(), 5U);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

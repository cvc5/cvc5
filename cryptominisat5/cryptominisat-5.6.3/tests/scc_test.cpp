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
#include <memory>

#include "src/solver.h"
#include "src/sccfinder.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

TEST(scc_test, find_1)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(2);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-1, -2"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 1U);
}

TEST(scc_test, find_2)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-1, -2"));

    s.add_clause_outer(str_to_cl("3, 4"));
    s.add_clause_outer(str_to_cl("-3, -4"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 2U);
}

TEST(scc_test, find_circle_3)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, -2"));
    s.add_clause_outer(str_to_cl("2, -3"));
    s.add_clause_outer(str_to_cl("3, -1"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 3U);
}

TEST(scc_test, find_two_circle2_3)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(6);
    s.add_clause_outer(str_to_cl("1, -2"));
    s.add_clause_outer(str_to_cl("2, -3"));
    s.add_clause_outer(str_to_cl("3, -1"));

    s.add_clause_outer(str_to_cl("4, -5"));
    s.add_clause_outer(str_to_cl("5, -6"));
    s.add_clause_outer(str_to_cl("6, -4"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 6U);
}

TEST(scc_test, find_1_diff)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(2);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-1, -2"));
    s.add_clause_outer(str_to_cl("1, -2"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 1U);
}

TEST(scc_test, find_0)
{
    SolverConf conf;
    conf.doCache = false;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("1, -2"));
    s.add_clause_outer(str_to_cl("3, -4"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 0U);
}


TEST(scc_test, limit_test4)
{
    SolverConf conf;
    conf.max_scc_depth = 4;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-2, 3"));
    s.add_clause_outer(str_to_cl("-3, -1"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 3U);
}

TEST(scc_test, limit_test3)
{
    SolverConf conf;
    conf.max_scc_depth = 3;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-2, 3"));
    s.add_clause_outer(str_to_cl("-3, -1"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 0U);
}

TEST(scc_test, limit_test2)
{
    SolverConf conf;
    conf.max_scc_depth = 2;

    std::unique_ptr<std::atomic<bool>> tmp(new std::atomic<bool>(false));
    Solver s(&conf, tmp.get());
    s.new_vars(4);
    s.add_clause_outer(str_to_cl("1, 2"));
    s.add_clause_outer(str_to_cl("-2, 3"));
    s.add_clause_outer(str_to_cl("-3, -1"));

    SCCFinder scc(&s);
    scc.performSCC();
    EXPECT_EQ(scc.get_binxors().size(), 0U);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

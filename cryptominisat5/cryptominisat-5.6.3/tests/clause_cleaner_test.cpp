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
#include "src/clausecleaner.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct clause_clean_test : public ::testing::Test {
    clause_clean_test()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCache = false;
        s = new Solver(&conf, &must_inter);
        s->new_vars(20);
        cc = s->clauseCleaner;
    }
    ~clause_clean_test()
    {
        delete s;
    }
    Solver* s = NULL;
    ClauseCleaner* cc = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(clause_clean_test, no_clean)
{
    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("1, 2"));

    cc->remove_and_clean_all();
    EXPECT_EQ(s->binTri.irredBins, 1U);
    std::string exp = "1, 2;  1, 2, 3";
    check_irred_cls_eq(s, exp);
}

TEST_F(clause_clean_test, clean_bin_pos)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("1"));
    check_irred_cls_eq(s, "1, 2");

    cc->remove_and_clean_all();
    EXPECT_EQ(s->binTri.irredBins, 0U);
}

TEST_F(clause_clean_test, clean_bin_neg)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1"));
    check_irred_cls_eq(s, "1, 2");

    cc->remove_and_clean_all();
    check_irred_cls_eq(s, "");
}

TEST_F(clause_clean_test, clean_tri_pos)
{
    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("1"));
    check_irred_cls_eq(s, "1, 2, 3");

    cc->remove_and_clean_all();
    check_irred_cls_eq(s, "");
}

TEST_F(clause_clean_test, clean_tri_neg)
{
    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("-1"));
    check_irred_cls_eq(s, "1, 2, 3");

    cc->remove_and_clean_all();
    EXPECT_EQ(s->binTri.irredBins, 1U);
    check_irred_cls_eq(s, "2, 3");
}

TEST_F(clause_clean_test, clean_long_pos)
{
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1"));
    check_irred_cls_eq(s, "1, 2, 3, 4");

    cc->remove_and_clean_all();
    check_irred_cls_eq(s, "");
}

TEST_F(clause_clean_test, clean_long_neg)
{
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("-1"));
    check_irred_cls_eq(s, "1, 2, 3, 4");

    cc->remove_and_clean_all();
    check_irred_cls_eq(s, "2, 3, 4");
}

TEST_F(clause_clean_test, clean_mix)
{
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("1, 9"));
    s->add_clause_outer(str_to_cl("-1"));
    check_irred_cls_eq(s, "1, 2, 3, 4; 1, 2, 3; 1, 9");

    cc->remove_and_clean_all();
    check_irred_cls_eq(s, "2, 3, 4; 2, 3");
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

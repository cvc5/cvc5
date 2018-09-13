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
#include "src/xorfinder.h"
#include "src/solverconf.h"
#include "src/occsimplifier.h"
using namespace CMSat;
#include "test_helper.h"
#include "src/toplevelgaussabst.h"
#ifdef USE_M4RI
#include "src/toplevelgauss.h"
#endif

struct xor_finder : public ::testing::Test {
    xor_finder()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCache = false;
        s = new Solver(&conf, &must_inter);
        s->new_vars(30);
        occsimp = s->occsimplifier;
    }
    ~xor_finder()
    {
        delete s;
    }
    Solver* s = NULL;
    OccSimplifier* occsimp = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(xor_finder, find_none)
{
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("-1, -2"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.grab_mem();
    finder.find_xors();
    EXPECT_EQ(finder.xors.size(), 0U);
}

TEST_F(xor_finder, find_tri_1)
{
    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("-1, -2, 3"));
    s->add_clause_outer(str_to_cl("-1, 2, -3"));
    s->add_clause_outer(str_to_cl("1, -2, -3"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_contains(finder.xors, "1, 2, 3 = 1");
}

TEST_F(xor_finder, find_tri_2)
{
    s->add_clause_outer(str_to_cl("-1, 2, 3"));
    s->add_clause_outer(str_to_cl("1, -2, 3"));
    s->add_clause_outer(str_to_cl("1, 2, -3"));
    s->add_clause_outer(str_to_cl("-1, -2, -3"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3 = 0");
}

TEST_F(xor_finder, find_tri_3)
{
    s->add_clause_outer(str_to_cl("-1, 2, 3"));
    s->add_clause_outer(str_to_cl("1, -2, 3"));
    s->add_clause_outer(str_to_cl("1, 2, -3"));
    s->add_clause_outer(str_to_cl("-1, -2, -3"));

    s->add_clause_outer(str_to_cl("1, 2, 3"));
    s->add_clause_outer(str_to_cl("-1, -2, 3"));
    s->add_clause_outer(str_to_cl("-1, 2, -3"));
    s->add_clause_outer(str_to_cl("1, -2, -3"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_contains(finder.xors, "1, 2, 3 = 0");
    check_xors_contains(finder.xors, "1, 2, 3 = 1");
}


TEST_F(xor_finder, find_4_1)
{
    s->add_clause_outer(str_to_cl("-1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 3, -4"));

    s->add_clause_outer(str_to_cl("1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, 4"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4 = 0;");
}

TEST_F(xor_finder, find_4_4)
{
    s->add_clause_outer(str_to_cl("-1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2,  -3, 4"));
    s->add_clause_outer(str_to_cl("-1, 2,  3, -4"));
    s->add_clause_outer(str_to_cl("1, -2,  3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4 = 1");
}

/*
 * These tests only work if the matching is non-exact
 * i.e. if size is not checked for equality
 */
TEST_F(xor_finder, find_4_2)
{
    s->add_clause_outer(str_to_cl("-1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 3"));

    s->add_clause_outer(str_to_cl("1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, 4"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4 = 0;");
}

TEST_F(xor_finder, find_4_3)
{
    s->add_clause_outer(str_to_cl("-1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 3"));

    s->add_clause_outer(str_to_cl("1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4"));
    s->add_clause_outer(str_to_cl("-1, -3, 4"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4 = 0;");
}

/*
//Finder pruning is too strong and we don't find this one
TEST_F(xor_finder, find_5_2)
{
    s->add_clause_outer(str_to_cl("-1, -2, 3, 4, 5"));
    s->add_clause_outer(str_to_cl("-1, 2, -3"));
    s->add_clause_outer(str_to_cl("-1, 2, 3"));

    s->add_clause_outer(str_to_cl("1, -2, -3, 4, 5"));
    s->add_clause_outer(str_to_cl("1, -2, 3, -4, 5"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4, -5"));

    s->add_clause_outer(str_to_cl("1, 2, -3, -4, 5"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4, -5"));

    s->add_clause_outer(str_to_cl("1, 2, 3, -4, -5"));

    //

    s->add_clause_outer(str_to_cl("1, -2, -3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, 4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, -4, 5"));

    s->add_clause_outer(str_to_cl("1, 2, 3, 4, 5"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4, 5 = 1;");
}*/

TEST_F(xor_finder, find_4_5)
{
    s->add_clause_outer(str_to_cl("-1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2,  -3, 4"));
    s->add_clause_outer(str_to_cl("-1, 2,  3, -4"));
    s->add_clause_outer(str_to_cl("1, -2,  3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("1, 2, 3"));

    s->add_clause_outer(str_to_cl("-1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 3"));

    s->add_clause_outer(str_to_cl("1, -2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4"));
    s->add_clause_outer(str_to_cl("-1, -3, 4"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4 = 1; 1, 2, 3, 4 = 0");
}
/***
 * Specialty, non-matching XOR test end
*/

TEST_F(xor_finder, find_5_1)
{
    s->add_clause_outer(str_to_cl("-1, -2, 3, 4, 5"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4, 5"));
    s->add_clause_outer(str_to_cl("-1, 2, 3, -4, 5"));
    s->add_clause_outer(str_to_cl("-1, 2, 3, 4, -5"));

    s->add_clause_outer(str_to_cl("1, -2, -3, 4, 5"));
    s->add_clause_outer(str_to_cl("1, -2, 3, -4, 5"));
    s->add_clause_outer(str_to_cl("1, -2, 3, 4, -5"));

    s->add_clause_outer(str_to_cl("1, 2, -3, -4, 5"));
    s->add_clause_outer(str_to_cl("1, 2, -3, 4, -5"));

    s->add_clause_outer(str_to_cl("1, 2, 3, -4, -5"));

    //

    s->add_clause_outer(str_to_cl("1, -2, -3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, 3, -4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, 4, -5"));
    s->add_clause_outer(str_to_cl("-1, -2, -3, -4, 5"));

    s->add_clause_outer(str_to_cl("1, 2, 3, 4, 5"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 2, 3, 4, 5 = 1;");
}


//we don't find 6-long, too expensive
/*TEST_F(xor_finder, find_6_0)
{
    s->add_clause_outer(str_to_cl("1, -7, -3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("-1, 7, -3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("-1, -7, 3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("1, 7, 3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("-1, -7, -3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("1, 7, -3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("1, -7, 3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("-1, 7, 3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("-1, -7, -3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("1, 7, -3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("1, -7, 3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("-1, 7, 3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("1, -7, -3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("-1, 7, -3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("-1, -7, 3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("1, 7, 3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("-1, -7, -3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("1, 7, -3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("1, -7, 3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("-1, 7, 3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("1, -7, -3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("-1, 7, -3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("-1, -7, 3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("1, 7, 3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("1, -7, -3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("-1, 7, -3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("-1, -7, 3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("1, 7, 3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("-1, -7, -3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("1, 7, -3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("1, -7, 3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("-1, 7, 3, 4, 5, 9"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "1, 7, 3, 4, 5, 9 = 0;");
}

TEST_F(xor_finder, find_6_1)
{
    s->add_clause_outer(str_to_cl("-6, -7, -3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("6, 7, -3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("6, -7, 3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("-6, 7, 3, -4, -5, -9"));
    s->add_clause_outer(str_to_cl("6, -7, -3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("-6, 7, -3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("-6, -7, 3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("6, 7, 3, 4, -5, -9"));
    s->add_clause_outer(str_to_cl("6, -7, -3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("-6, 7, -3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("-6, -7, 3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("6, 7, 3, -4, 5, -9"));
    s->add_clause_outer(str_to_cl("-6, -7, -3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("6, 7, -3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("6, -7, 3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("-6, 7, 3, 4, 5, -9"));
    s->add_clause_outer(str_to_cl("6, -7, -3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("-6, 7, -3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("-6, -7, 3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("6, 7, 3, -4, -5, 9"));
    s->add_clause_outer(str_to_cl("-6, -7, -3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("6, 7, -3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("6, -7, 3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("-6, 7, 3, 4, -5, 9"));
    s->add_clause_outer(str_to_cl("-6, -7, -3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("6, 7, -3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("6, -7, 3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("-6, 7, 3, -4, 5, 9"));
    s->add_clause_outer(str_to_cl("6, -7, -3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("-6, 7, -3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("-6, -7, 3, 4, 5, 9"));
    s->add_clause_outer(str_to_cl("6, 7, 3, 4, 5, 9"));

    occsimp->setup();
    XorFinder finder(occsimp, s);
    finder.find_xors();
    check_xors_eq(finder.xors, "6, 7, 3, 4, 5, 9 = 1;");
}*/

struct xor_finder2 : public ::testing::Test {
    xor_finder2()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doCache = false;
        s = new Solver(&conf, &must_inter);
        s->new_vars(30);
        occsimp = s->occsimplifier;
        finder = new XorFinder(occsimp, s);
        finder->grab_mem();
        #ifdef USE_M4RI
        topLevelGauss = new TopLevelGauss(s);
        #endif
    }
    ~xor_finder2()
    {
        delete s;
        delete finder;
        #ifdef USE_M4RI
        delete topLevelGauss;
        #endif
    }
    Solver* s = NULL;
    OccSimplifier* occsimp = NULL;
    std::atomic<bool> must_inter;
    XorFinder* finder;
    #ifdef USE_M4RI
    TopLevelGaussAbst *topLevelGauss;
    #endif
};


TEST_F(xor_finder2, clean_v1)
{
    finder->xors = str_to_xors("1, 2, 3 = 0;");
    finder->xors = finder->remove_xors_without_connecting_vars(finder->xors);
    EXPECT_EQ(finder->xors.size(), 0u);
}

TEST_F(xor_finder2, clean_v2)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 4, 5, 6 = 0");
    finder->xors = finder->remove_xors_without_connecting_vars(finder->xors);
    EXPECT_EQ(finder->xors.size(), 2u);
}

TEST_F(xor_finder2, clean_v3)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 4, 5, 6 = 0; 10, 11, 12, 13 = 1");
    finder->xors = finder->remove_xors_without_connecting_vars(finder->xors);
    EXPECT_EQ(finder->xors.size(), 2u);
}

TEST_F(xor_finder2, clean_v4)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 4, 5, 6 = 0; 10, 11, 12, 13 = 1; 10, 15, 16, 17 = 0");
    finder->xors = finder->remove_xors_without_connecting_vars(finder->xors);
    EXPECT_EQ(finder->xors.size(), 4u);
}

TEST_F(xor_finder2, xor_1)
{
    finder->xors = str_to_xors("1, 2, 3 = 1; 1, 4, 5, 6 = 0;");
    finder->xor_together_xors(finder->xors);
    check_xors_eq(finder->xors, "2, 3, 4, 5, 6 = 1;");
}

TEST_F(xor_finder2, xor_2)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 4, 5, 6 = 0;");
    finder->xor_together_xors(finder->xors);
    check_xors_eq(finder->xors, "2, 3, 4, 5, 6 = 0;");
}

TEST_F(xor_finder2, xor_3)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 10, 4, 5, 6 = 0;");
    finder->xor_together_xors(finder->xors);
    check_xors_eq(finder->xors, "1, 2, 3 = 0; 10, 4, 5, 6 = 0;");
}

TEST_F(xor_finder2, xor_4)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 4, 5, 6 = 0;"
        "1, 9, 10, 11 = 0;");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 3u);
}

TEST_F(xor_finder2, xor_5)
{
    finder->xors = str_to_xors("2, 3, 1 = 0; 1, 5, 6, 4 = 0;" "4, 10, 11 = 0;");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 1u);
    check_xors_contains(finder->xors, "2, 3, 5, 6, 10, 11 = 0");
}

TEST_F(xor_finder2, xor_6)
{
    finder->xors = str_to_xors("1, 2 = 0; 1, 4= 0;"
        "6, 7 = 0; 6, 10 = 1");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 2u);
    check_xors_eq(finder->xors, "2, 4 = 0; 7, 10 = 1");
}

TEST_F(xor_finder2, dont_xor_together_when_clash_more_than_one)
{
    finder->xors = str_to_xors("1, 2, 3, 4 = 0; 1, 2, 5, 6= 0;");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 2u);
    check_xors_eq(finder->xors, "1, 2, 3, 4 = 0; 1, 2, 5, 6= 0;");
}

TEST_F(xor_finder2, dont_remove_xors)
{
    finder->xors = str_to_xors("1, 2 = 0; 1, 2= 0;");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 1U);
}

TEST_F(xor_finder2, dont_remove_xors2)
{
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 2, 3= 0;");
    finder->xor_together_xors(finder->xors);
    EXPECT_EQ(finder->xors.size(), 1U);
}

TEST_F(xor_finder2, xor_pure_unit_unsat)
{
    finder->xors = str_to_xors("1 = 0; 1 = 1;");
    finder->xor_together_xors(finder->xors);
    bool ret = finder->add_new_truths_from_xors(finder->xors);
    EXPECT_FALSE(ret);
}

TEST_F(xor_finder2, xor_8)
{
    finder->xors = str_to_xors("1, 2 = 0; 1 = 1; 2 = 0");
    bool ret = finder->xor_together_xors(finder->xors);
    EXPECT_TRUE(ret);
    EXPECT_EQ(finder->xors.size(), 1U);

    ret = finder->add_new_truths_from_xors(finder->xors);
    EXPECT_FALSE(ret);
}

TEST_F(xor_finder2, xor_unit)
{
    finder->xors = str_to_xors("1 = 0; 1, 2, 3 = 1; 3 = 1");
    finder->xor_together_xors(finder->xors);
    bool ret = finder->add_new_truths_from_xors(finder->xors);
    EXPECT_TRUE(ret);
    EXPECT_EQ(finder->xors.size(), 0u);
}

#ifdef USE_M4RI
TEST_F(xor_finder2, xor_unit2_2)
{
    s->add_clause_outer(str_to_cl("-4"));
    finder->xors = str_to_xors("1, 2, 3 = 0; 1, 2, 3, 4 = 1;");
    vector<Lit> out_changed_occur;
    bool ret = topLevelGauss->toplevelgauss(finder->xors, &out_changed_occur);
    EXPECT_FALSE(ret);
}
#endif

TEST_F(xor_finder2, xor_binx)
{
    finder->xors = str_to_xors("1, 2, 5 = 0; 1, 3 = 0; 2 = 0");
    bool ret = finder->xor_together_xors(finder->xors);
    if (ret) {
        ret &= finder->add_new_truths_from_xors(finder->xors);
    }
    EXPECT_TRUE(ret);
    EXPECT_EQ(finder->xors.size(), 0u);
    check_red_cls_eq(s, "5, -3; -5, 3");
}

TEST_F(xor_finder2, xor_binx_inv_not_found)
{
    finder->xors = str_to_xors("3, 1 = 1; 1, 3 = 0;");
    bool ret = finder->xor_together_xors(finder->xors);
    if (ret) {
        ret &= finder->add_new_truths_from_xors(finder->xors);
    }
    EXPECT_TRUE(ret);
}

TEST_F(xor_finder2, xor_recur_bug)
{
    finder->xors = str_to_xors("3, 7, 9 = 0; 1, 3, 4, 5 = 1;");
    bool ret = finder->xor_together_xors(finder->xors);
    EXPECT_TRUE(ret);
    check_xors_eq(finder->xors, "7, 9 , 1, 4, 5 = 1;");
}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

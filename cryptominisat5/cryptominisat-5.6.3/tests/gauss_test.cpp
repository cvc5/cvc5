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
#include "src/EGaussian.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct gauss : public ::testing::Test {
    gauss()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        //conf.verbosity = 20;
        s = new Solver(&conf, &must_inter);
        s->new_vars(30);
    }
    ~gauss()
    {
        delete g;
        delete s;
    }

    Solver* s;
    Gaussian* g = NULL;
    std::vector<uint32_t> vars;
    std::atomic<bool> must_inter;
    vector<Xor> xs;
    bool created;
};

//2 XORs inside

TEST_F(gauss, propagate_1)
{
    s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("1, 2, 3, 4"), 0));

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, true);
    EXPECT_EQ(s->ok, true);
    check_zero_assigned_lits_eq(s, "-4");
}

TEST_F(gauss, propagate_2)
{
    //s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("1, 2, 3, 4"), 1));

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, true);
    EXPECT_EQ(s->ok, true);
    check_zero_assigned_lits_eq(s, "4");
}

TEST_F(gauss, propagate_3)
{
    //s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 3, 4, 5"), 0));
    xs.push_back(Xor(str_to_vars("1, 3, 5"), 1));

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, true);
    EXPECT_EQ(s->ok, true);
    check_zero_assigned_lits_eq(s, "4");
}

TEST_F(gauss, propagate_4)
{
    //s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 3, 4, 5"), 0));
    xs.push_back(Xor(str_to_vars("1, 3, 5"), 1));
    xs.push_back(Xor(str_to_vars("1, 2, 4, 7"), 1));

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, true);
    EXPECT_EQ(s->ok, true);
    check_zero_assigned_lits_eq(s, "4");
}

//UNSAT

TEST_F(gauss, unsat_4)
{
    //s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 3, 5"), 0));
    xs.push_back(Xor(str_to_vars("1, 3, 5"), 1));

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, false);
    EXPECT_EQ(s->ok, false);
}

//double prop

TEST_F(gauss, propagate_unsat)
{
    //s->conf.verbosity = 20;
    xs.push_back(Xor(str_to_vars("1, 3, 4, 5"), 0));
    xs.push_back(Xor(str_to_vars("1, 3, 5"), 0));
    //-> 4 = 0
    xs.push_back(Xor(str_to_vars("5, 6, 7"), 1));
    xs.push_back(Xor(str_to_vars("4, 5, 6, 7"), 0));
    //-> unsat

    g = new Gaussian(s, xs, 0);
    bool ret = g->init_until_fixedpoint(created);

    EXPECT_EQ(ret, false);
    EXPECT_EQ(s->ok, false);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

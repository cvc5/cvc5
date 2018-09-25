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
#include "src/matrixfinder.h"
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
        s->new_vars(40);
        s->conf.gaussconf.min_gauss_xor_clauses = 0;
        mf = new MatrixFinder(s);
    }
    ~gauss()
    {
        delete s;
    }

    Solver* s;
    MatrixFinder* mf = NULL;
    std::vector<uint32_t> vars;
    std::atomic<bool> must_inter;
    vector<Xor> xs;
};

TEST_F(gauss, min_rows)
{
    //s->conf.verbosity = 20;
    s->conf.gaussconf.min_matrix_rows = 2;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("1, 2, 3, 4"), 0));
    s->xorclauses = xs;

    mf->findMatrixes(false);

    EXPECT_EQ(s->gmatrixes.size(), 1);
}

TEST_F(gauss, min_rows_2)
{
    //s->conf.verbosity = 20;
    s->conf.gaussconf.min_matrix_rows = 3;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("1, 2, 3, 4"), 0));
    s->xorclauses = xs;

    mf->findMatrixes(false);

    EXPECT_EQ(s->gmatrixes.size(), 0);
}

TEST_F(gauss, separate_1)
{
    //s->conf.verbosity = 20;
    s->conf.gaussconf.min_matrix_rows = 1;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("5, 6, 7, 8"), 0));
    s->xorclauses = xs;

    mf->findMatrixes(false);

    EXPECT_EQ(s->gmatrixes.size(), 2);
}

TEST_F(gauss, separate_2)
{
    //s->conf.verbosity = 20;
    s->conf.gaussconf.min_matrix_rows = 1;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("4, 5, 6"), 0));
    xs.push_back(Xor(str_to_vars("3, 4, 10"), 0));

    xs.push_back(Xor(str_to_vars("15, 16, 17, 18"), 0));
    xs.push_back(Xor(str_to_vars("11, 15, 19"), 0));
    xs.push_back(Xor(str_to_vars("19, 20, 12"), 0));
    s->xorclauses = xs;

    mf->findMatrixes(false);

    EXPECT_EQ(s->gmatrixes.size(), 2);
}

TEST_F(gauss, separate_3)
{
    //s->conf.verbosity = 20;
    s->conf.gaussconf.min_matrix_rows = 1;
    xs.push_back(Xor(str_to_vars("1, 2, 3"), 0));
    xs.push_back(Xor(str_to_vars("4, 5, 6"), 0));
    xs.push_back(Xor(str_to_vars("3, 4, 10"), 0));

    xs.push_back(Xor(str_to_vars("15, 16, 17, 18"), 0));
    xs.push_back(Xor(str_to_vars("11, 15, 19"), 0));
    xs.push_back(Xor(str_to_vars("19, 20, 12"), 0));

    xs.push_back(Xor(str_to_vars("21, 22, 23, 29"), 0));
    xs.push_back(Xor(str_to_vars("21, 28, 29"), 0));
    xs.push_back(Xor(str_to_vars("25, 21, 27"), 0));
    s->xorclauses = xs;

    mf->findMatrixes(false);

    EXPECT_EQ(s->gmatrixes.size(), 3);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

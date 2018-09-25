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
#include <stdlib.h>

#include "src/solver.h"
#include "src/clauseallocator.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct clause_allocator : public ::testing::Test {
    clause_allocator()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.verbosity = 1;
        s = new Solver(&conf, &must_inter);
        s->new_vars(50000);
    }
    ~clause_allocator()
    {
        delete s;
    }
    Solver* s = NULL;
    std::atomic<bool> must_inter;
};

TEST_F(clause_allocator, add_1)
{
    vector<Lit> cl;
    srand(0);
    double t = cpuTime();

    uint64_t num = 10ULL*1000ULL*1000ULL;
    for(size_t i = 0; i < num; i++) {
        int size = 100 + rand()%10;
        int start = rand() % 50000/size;
        cl.resize(size);
        for(int i2 = 0; i2 < size; i2++) {
            int sign = rand() % 2;
            cl[i2] = Lit(start, sign);
            start += rand() % (50000/size);
        }
        s->add_clause_outer(cl);
        if (i % (300ULL*1000ULL) == 0) {
            cout << "Added " << i/(3000LL*1000ULL) << "M" << " T:" << (cpuTime()-t) << endl;
            s->cl_alloc.consolidate(s, true);
        }
    }
    s->cl_alloc.consolidate(s, true);
    lbool ret = s->solve_with_assumptions(NULL);
    EXPECT_EQ(ret, l_True);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

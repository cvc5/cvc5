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
#include "src/subsumeimplicit.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct sub_impl : public ::testing::Test {
    sub_impl()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        //conf.verbosity = 20;
        s = new Solver(&conf, &must_inter);
        sub = s->subsumeImplicit;
    }
    ~sub_impl()
    {
        delete s;
    }

    Solver* s;
    SubsumeImplicit* sub;
    std::atomic<bool> must_inter;
};

//SUB 2-by-2
TEST_F(sub_impl, sub_2by2_1)
{
    s->new_vars(7);
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("1, -2"));

    sub->subsume_implicit();
    check_irred_cls_eq(s, "1, -2");
}

TEST_F(sub_impl, sub_2by2_2)
{
    s->new_vars(7);
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("1, 3"));
    s->add_clause_outer(str_to_cl("1, -4"));
    s->add_clause_outer(str_to_cl("1, -2"));

    sub->subsume_implicit();
    check_irred_cls_eq(s, "1, -2; 1, 3; 1, -4");
}

TEST_F(sub_impl, sub_2by2_3)
{
    s->new_vars(7);
    s->add_clause_outer(str_to_cl("2, 1"));
    s->add_clause_outer(str_to_cl("2, 4"));
    s->add_clause_outer(str_to_cl("1, 3"));
    s->add_clause_outer(str_to_cl("1, 3"));
    s->add_clause_outer(str_to_cl("-1, -3"));
    s->add_clause_outer(str_to_cl("1, 2"));

    sub->subsume_implicit();
    check_irred_cls_eq(s, "1, 2; 1, 3;2, 4;-1, -3");
}

TEST_F(sub_impl, sub_2by2_4)
{
    s->new_vars(7);
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 4"));
    s->add_clause_outer(str_to_cl("-1, 2, 4"));
    s->add_clause_outer(str_to_cl("1, 4"));

    sub->subsume_implicit();
    check_irred_cls_eq(s, "1, 4; 1, 2, 3, 4;-1, 2, 4");
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

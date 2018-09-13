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
#include "src/distillerlongwithimpl.h"
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

struct distill_long_with_impl : public ::testing::Test {
    distill_long_with_impl()
    {
        must_inter.store(false, std::memory_order_relaxed);
        SolverConf conf;
        conf.doStamp = true;
        conf.doCache = true;
        conf.otfHyperbin - true;
        //conf.verbosity = 20;
        s = new Solver(&conf, &must_inter);
        distillwbin = s->dist_long_with_impl;
    }
    ~distill_long_with_impl()
    {
        delete s;
    }

    Solver* s;
    DistillerLongWithImpl* distillwbin;
    std::atomic<bool> must_inter;
};

//Subsume long with bin

TEST_F(distill_long_with_impl, subsume_w_bin)
{
    s->new_vars(4);
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "1, 2");
}

TEST_F(distill_long_with_impl, subsume_w_bin2)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("1, 2, 4, -5"));

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "1, 2");
}

TEST_F(distill_long_with_impl, subsume_w_bin3)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("2, 3"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));
    s->add_clause_outer(str_to_cl("2, 3, -4, 5"));

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "2, 3");
}

//No subsumption

TEST_F(distill_long_with_impl, no_subsume)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("2, 3, 4, 5"));

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "1, 2; 2, 3, 4, 5");
}

TEST_F(distill_long_with_impl, no_subsume_tri)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("1, 2"));
    s->add_clause_outer(str_to_cl("2, 3, 4, 5"));

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "1, 2; 2, 3, 4, 5");
}

//Strengthening long with bin

TEST_F(distill_long_with_impl, str_w_bin)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("1, -2"));
    s->add_clause_outer(str_to_cl("1, 2, 3, 4"));

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_contains(s, "1, 3, 4");
}

TEST_F(distill_long_with_impl, str_w_bin2)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, -2"));
    s->add_clause_outer(str_to_cl("-1, 2, 3, 4"));

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_contains(s, "-1, 3, 4");
}

TEST_F(distill_long_with_impl, str_w_bin3)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-2, -3"));
    s->add_clause_outer(str_to_cl("-2, 3, 4, 5"));
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_contains(s, "-2, 4, 5");
    check_irred_cls_contains(s, "-1, -3, 4");
}

//Subsume with cache

TEST_F(distill_long_with_impl, sub_w_cache)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));
    add_to_cache_irred(s, "2, -3");

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "");
}

TEST_F(distill_long_with_impl, sub_w_cache2)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));
    add_to_cache_irred(s, "2, 4");

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "");
}

//STR with cache

TEST_F(distill_long_with_impl, str_w_cache)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));
    add_to_cache_irred(s, "-1, -2");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "-1, -3, 4");
}

TEST_F(distill_long_with_impl, str_w_cache2)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("2, -3, 4, 5"));
    add_to_cache_irred(s, "4, -5");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "2, -3, 4");
}

TEST_F(distill_long_with_impl, str_w_cache_no)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("2, -3, 4, 5"));
    add_to_cache_irred(s, "4, -1");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "2, -3, 4, 5");
}

//SUB with stamp

TEST_F(distill_long_with_impl, sub_w_stamp)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));
    add_to_stamp_irred(s, "-1, 2");

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "");
}

TEST_F(distill_long_with_impl, sub_w_stamp2)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 3, 4, 5"));
    add_to_stamp_irred(s, "3, -1");

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "");
}

TEST_F(distill_long_with_impl, sub_w_stamp_no)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("-1, 2, -3, 4"));
    add_to_stamp_irred(s, "-2, -1");

    distillwbin->distill_long_with_implicit(false);
    check_irred_cls_eq(s, "-1, 2, -3, 4");
}

// //STR with stamp

TEST_F(distill_long_with_impl, str_w_stamp)
{
    s->new_vars(5);
    s->add_clause_outer(str_to_cl("2, -3, 4, 5"));
    add_to_stamp_irred(s, "2, 3");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "2, 4, 5");
}

TEST_F(distill_long_with_impl, str_w_stamp2)
{
    s->new_vars(10);
    s->add_clause_outer(str_to_cl("-1, 7, 8, -9"));
    add_to_stamp_irred(s, "1, 7");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "7, 8, -9");
}

TEST_F(distill_long_with_impl, str_w_stamp_no)
{
    s->new_vars(10);
    s->add_clause_outer(str_to_cl("-3, 6, 7, -9"));
    add_to_stamp_irred(s, "3, -6");

    distillwbin->distill_long_with_implicit(true);
    check_irred_cls_eq(s, "-3, 6, 7, -9");
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

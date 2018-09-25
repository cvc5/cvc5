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
#include "src/solverconf.h"
using namespace CMSat;
#include "test_helper.h"

namespace CMSat {
struct SolverTest : public ::testing::Test {
    SolverTest()
    {
        must_inter.store(false, std::memory_order_relaxed);
    }
    ~SolverTest()
    {
        delete s;
    }

    SolverConf conf;
    Solver* s = NULL;
    std::vector<uint32_t> vars;
    std::atomic<bool> must_inter;
};

TEST_F(SolverTest, get_bin)
{
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    s->add_clause_outer(str_to_cl(" 2,  3"));
    s->add_clause_int(str_to_cl(" 1,  2"), true);

    s->start_getting_small_clauses(2, 100);
    vector<Lit> lits;
    bool ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 1,  2"));

    ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

TEST_F(SolverTest, get_long_lev0)
{
    Clause* c;
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 5;

    s->add_clause_outer(str_to_cl(" 2,  3"));
    c = s->add_clause_int(str_to_cl(" 1,  2, 3, 4"), true, stats);
    assert(c != NULL);
    s->longRedCls[0].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(10, 100);
    vector<Lit> lits;

    bool ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 1,  2, 3, 4"));

    ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}


TEST_F(SolverTest, get_long_lev1)
{
    Clause* c;
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 5;

    s->add_clause_outer(str_to_cl(" 2,  3"));
    c = s->add_clause_int(str_to_cl(" 6,  2, 3, 4"), true, stats);
    assert(c != NULL);
    s->longRedCls[1].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(10, 100);
    vector<Lit> lits;

    bool ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 6,  2, 3, 4"));

    ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

TEST_F(SolverTest, get_long_lev0_and_lev1)
{
    Clause* c;
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 5;

    s->add_clause_outer(str_to_cl(" 2,  3"));

    c = s->add_clause_int(str_to_cl(" 3, -4, -7"), true, stats);
    assert(c != NULL);
    s->longRedCls[1].push_back(s->cl_alloc.get_offset(c));

    c = s->add_clause_int(str_to_cl(" 2, 4, 5, 6"), true, stats);
    assert(c != NULL);
    s->longRedCls[0].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(10, 100);
    vector<Lit> lits;

    //Order is reverse because we get lev0 then lev1
    bool ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 2, 4, 5, 6"));

    ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 3, -4, -7"));

    ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

TEST_F(SolverTest, get_long_toolarge)
{
    Clause* c;
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 5;

    s->add_clause_outer(str_to_cl(" 2,  3"));
    c = s->add_clause_int(str_to_cl(" 1,  2, 3, 4"), true, stats);
    assert(c != NULL);
    s->longRedCls[0].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(2, 100);
    vector<Lit> lits;

    bool ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

TEST_F(SolverTest, get_glue_toolarge)
{
    Clause* c;
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 20;

    s->add_clause_outer(str_to_cl(" 2,  3"));
    c = s->add_clause_int(str_to_cl(" 1,  2, 3, 4"), true, stats);
    assert(c != NULL);
    s->longRedCls[0].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(100, 2);
    vector<Lit> lits;

    bool ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

TEST_F(SolverTest, get_bin_and_long)
{
    s = new Solver(&conf, &must_inter);
    s->new_vars(30);
    ClauseStats stats;
    stats.glue = 5;

    s->add_clause_outer(str_to_cl(" 2,  3"));
    Clause* c;
    c = s->add_clause_int(str_to_cl(" 1,  5 "), true);
    assert(c == NULL);
    c = s->add_clause_int(str_to_cl(" 1,  2, 3, 4"), true, stats);
    assert(c != NULL);
    s->longRedCls[0].push_back(s->cl_alloc.get_offset(c));

    s->start_getting_small_clauses(4, 100);
    vector<Lit> lits;

    bool ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 1,  5"));

    ret = s->get_next_small_clause(lits);
    ASSERT_TRUE(ret);
    std::sort(lits.begin(), lits.end());
    ASSERT_EQ(lits, str_to_cl(" 1,  2, 3, 4"));

    ret = s->get_next_small_clause(lits);
    ASSERT_FALSE(ret);

    s->end_getting_small_clauses();
}

}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

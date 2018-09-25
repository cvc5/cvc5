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

#include "cryptominisat5/cryptominisat.h"
#include "src/solverconf.h"
#include <vector>
using std::vector;
using namespace CMSat;

struct assump_interf : public ::testing::Test {
    assump_interf()
    {
        SolverConf conf;
        s = new SATSolver(&conf);
    }
    ~assump_interf()
    {
        delete s;
    }
    SATSolver* s = NULL;
    vector<Lit> assumps;
};

TEST_F(assump_interf, empty)
{
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false)});
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_True);
    EXPECT_EQ( s->okay(), true);
}

TEST_F(assump_interf, single_true)
{
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false)});
    assumps.push_back(Lit(0, false));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_True);
    EXPECT_EQ( s->okay(), true);
}

TEST_F(assump_interf, single_false)
{
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false)});
    assumps.push_back(Lit(0, true));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->get_conflict().size(), 1u);
    EXPECT_EQ( s->get_conflict()[0], Lit(0, false));
}


TEST_F(assump_interf, single_false_then_true)
{
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false)});
    assumps.push_back(Lit(0, true));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->okay(), true);

    ret = s->solve();
    EXPECT_EQ( ret, l_True);
    EXPECT_EQ( s->okay(), true);

}

TEST_F(assump_interf, binclause_true)
{
    s->new_var();
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false), Lit(1, false)});
    assumps.push_back(Lit(0, true));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_True );
    EXPECT_EQ( s->get_model()[0], l_False );
    EXPECT_EQ( s->get_model()[1], l_True );
}

TEST_F(assump_interf, binclause_false)
{
    s->new_var();
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false), Lit(1, false)});
    assumps.push_back(Lit(0, true));
    assumps.push_back(Lit(1, true));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->get_conflict().size(), 2u);

    vector<Lit> tmp = s->get_conflict();
    std::sort(tmp.begin(), tmp.end());
    EXPECT_EQ( tmp[0], Lit(0, false) );
    EXPECT_EQ( tmp[1], Lit(1, false) );
}

TEST_F(assump_interf, replace_true)
{
    s->new_var();
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false), Lit(1, true)});
    s->add_clause(vector<Lit>{Lit(0, true), Lit(1, false)});
    assumps.push_back(Lit(0, true));
    assumps.push_back(Lit(1, true));
    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_True);
    EXPECT_EQ( s->get_model()[0], l_False );
    EXPECT_EQ( s->get_model()[1], l_False );

    assumps.clear();
    assumps.push_back(Lit(0, true));
    assumps.push_back(Lit(1, false));
    ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
}

TEST_F(assump_interf, replace_false)
{
    s->new_var();
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false), Lit(1, true)}); //a V -b
    s->add_clause(vector<Lit>{Lit(0, true), Lit(1, false)}); //-a V b
    //a == b

    assumps.push_back(Lit(0, false));
    assumps.push_back(Lit(1, true));
    //a = 1, b = 0

    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->okay(), true);

    EXPECT_EQ( s->get_conflict().size(), 2u);

    vector<Lit> tmp = s->get_conflict();
    std::sort(tmp.begin(), tmp.end());
    EXPECT_EQ( tmp[0], Lit(0, true) );
    EXPECT_EQ( tmp[1], Lit(1, false) );
}

TEST_F(assump_interf, set_var_by_prop)
{
    s->new_var();
    s->new_var();
    s->add_clause(vector<Lit>{Lit(0, false)}); //a = 1
    s->add_clause(vector<Lit>{Lit(0, true), Lit(1, false)}); //-a V b
    //-> b = 1

    assumps.push_back(Lit(1, true));
    //b = 0

    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->okay(), true);

    EXPECT_EQ( s->get_conflict().size(), 1u);

    vector<Lit> tmp = s->get_conflict();
    EXPECT_EQ( tmp[0], Lit(1, false) );
}

TEST_F(assump_interf, only_assump)
{
    s->new_var();
    s->new_var();

    assumps.push_back(Lit(1, true));
    assumps.push_back(Lit(1, false));

    lbool ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
    EXPECT_EQ( s->okay(), true);
    EXPECT_EQ( s->get_conflict().size(), 2u);

    vector<Lit> tmp = s->get_conflict();
    std::sort(tmp.begin(), tmp.end());
    EXPECT_EQ( tmp[0] , Lit(1, false) );
    EXPECT_EQ( tmp[1], Lit(1, true) );

    ret = s->solve(NULL);
    EXPECT_EQ( ret, l_True );

    ret = s->solve(&assumps);
    EXPECT_EQ( ret, l_False);
}


int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

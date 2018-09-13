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

#include "cryptominisat5/cryptominisat.h"
#include "src/solverconf.h"
#include "test_helper.h"
using namespace CMSat;
#include <vector>
using std::vector;

struct dump : public ::testing::Test {
    dump() {
        fname = string("test-cnf-dump");
    }

    ~dump() {
        std::remove(fname.c_str());
    }

    void read_dat() {
        s.open_file_and_dump_irred_clauses(fname);
        dat = cnf_file_read(fname);
    }

    SATSolver s;
    string fname;
    cnfdata dat;
};


TEST_F(dump, empty_cnf)
{
    lbool ret = s.solve();
    EXPECT_EQ( ret, l_True);

    read_dat();
    EXPECT_EQ(dat.num_vars, 0);
    EXPECT_EQ(dat.cls.size(), 0);
}

TEST_F(dump, onelit)
{
    s.new_var();
    s.add_clause(str_to_cl("1"));
    s.solve();

    read_dat();
    EXPECT_EQ(dat.num_vars, 1);
    EXPECT_EQ(dat.cls.size(), 1);
    EXPECT_TRUE(cl_eq(dat.cls[0], str_to_cl("1")));
}

TEST_F(dump, twolit)
{
    s.new_vars(2);
    s.add_clause(str_to_cl("1"));
    s.add_clause(str_to_cl("1, 2"));
    s.solve();


    read_dat();
    EXPECT_EQ(dat.num_vars, 1);
    EXPECT_EQ(dat.cls.size(), 1);
    EXPECT_TRUE(cl_eq(dat.cls[0], str_to_cl("1")));
}

TEST_F(dump, longcls)
{
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2, 3, 4"));
    s.add_clause(str_to_cl("-4"));
    s.simplify();


    read_dat();
    EXPECT_EQ(dat.num_vars, 4);
    EXPECT_EQ(dat.cls.size(), 2);
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("-4")));
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("1,2,3")));
}

TEST_F(dump, eqcls)
{
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2"));
    s.add_clause(str_to_cl("-1, -2"));
    s.simplify();


    read_dat();
    EXPECT_EQ(dat.cls.size(), 2);
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("1,2")));
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("-1,-2")));
}

TEST_F(dump, eqcls2)
{
    s.new_vars(4);
    s.add_clause(str_to_cl("-1, 2"));
    s.add_clause(str_to_cl("1, -2"));
    s.simplify();


    read_dat();
    EXPECT_EQ(dat.cls.size(), 2);
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("-1,2")));
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("1,-2")));
}

TEST_F(dump, subsume)
{
    s.new_vars(4);
    s.add_clause(str_to_cl("-1, -2, 3"));
    s.add_clause(str_to_cl("-1, -2"));
    s.simplify();


    read_dat();
    EXPECT_EQ(dat.cls.size(), 1);
    EXPECT_TRUE(cl_exists(dat.cls, str_to_cl("-1,-2")));
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

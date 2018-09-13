/******************************************
Copyright (c) 2014, Mate Soos

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

#include "src/clause.h"
#include <sstream>
#include <stdlib.h>

using namespace CMSat;

struct F : public ::testing::Test {
    F() {
    }

    ~F() {
    }

    Clause* allocate_space_for(size_t n, void*& tmp)
    {
        tmp = malloc(sizeof(Clause) + n*sizeof(Lit));
        std::vector<Lit> lits;
        for(size_t i = 0; i < n ; i++) {
            lits.push_back(Lit(i, false));
        }
        Clause* c_ptr = new(tmp) Clause(lits
        , 0
        #ifdef STATS_NEEDED
        , 0
        #endif
        );
        return c_ptr;
    }
};

TEST_F(F, convert_to_string)
{
    void* tmp;
    Clause& cl = *allocate_space_for(3, tmp);
    cl[0] = Lit(0, false);
    cl[1] = Lit(1, false);
    cl[2] = Lit(2, false);

    std::stringstream ss;
    ss << cl;
    EXPECT_EQ( ss.str(), "1 2 3");
    free(tmp);
}

TEST_F(F, convert_to_string2)
{
    void* tmp;
    Clause& cl = *allocate_space_for(3, tmp);
    cl[0] = Lit(0, false);
    cl[1] = Lit(1, true);
    cl[2] = Lit(2, false);

    std::stringstream ss;
    ss << cl;
    EXPECT_EQ( ss.str(), "1 -2 3");
    free(tmp);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

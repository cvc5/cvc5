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

#ifndef __DISTILLER_IMPL_WITH_IMP__
#define __DISTILLER_IMPL_WITH_IMP__

#include <vector>
#include "clause.h"
#include "constants.h"
#include "solvertypes.h"
#include "cloffset.h"
#include "watcharray.h"
using std::vector;

namespace CMSat {

class Solver;
class Clause;

class StrImplWImplStamp {
public:
    explicit StrImplWImplStamp(Solver* _solver) :
        solver(_solver)
    {}

    bool str_impl_w_impl_stamp();
    double mem_used() const;

private:
    Solver* solver;
    void distill_implicit_with_implicit_lit(const Lit lit);

    void strengthen_bin_with_bin(
        const Lit lit
        , Watched* i
        , Watched*& j
        , const Watched* end
    );

    //Vars for strengthen implicit
    struct StrImplicitData
    {
        uint64_t remLitFromBin = 0;
        uint64_t stampRem = 0;

        uint64_t numWatchesLooked = 0;

        //For delayed enqueue and binary adding
        //Used for strengthening
        vector<Lit> toEnqueue;
        vector<BinaryClause> binsToAdd;

        void clear()
        {
            StrImplicitData tmp;
            *this = tmp;
        }

        void print(
            const size_t trail_diff
            , const double time_used
            , const int64_t timeAvailable
            , const int64_t orig_time
            , Solver* solver
        ) const;
    };
    StrImplicitData str_impl_data;
    int64_t timeAvailable;
    vector<Lit> lits;
};

}

#endif // __DISTILLER_IMPL_WITH_IMP__

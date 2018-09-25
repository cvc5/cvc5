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

#ifndef __DISTILLERALL_WITH_ALL_H__
#define __DISTILLERALL_WITH_ALL_H__

#include <vector>
#include "clause.h"
#include "constants.h"
#include "solvertypes.h"
#include "cloffset.h"
#include "watcharray.h"

namespace CMSat {

using std::vector;

class Solver;
class Clause;

class DistillerLong {
    public:
        explicit DistillerLong(Solver* solver);
        bool distill(const bool red);

        struct Stats
        {
            void clear()
            {
                Stats tmp;
                *this = tmp;
            }

            Stats& operator+=(const Stats& other);
            void print_short(const Solver* solver) const;
            void print(const size_t nVars) const;

            double time_used = 0.0;
            uint64_t timeOut = 0;
            uint64_t zeroDepthAssigns = 0;
            uint64_t numClShorten = 0;
            uint64_t numLitsRem = 0;
            uint64_t checkedClauses = 0;
            uint64_t potentialClauses = 0;
            uint64_t numCalled = 0;
        };

        const Stats& get_stats() const;
        double mem_used() const;

    private:

        ClOffset try_distill_clause_and_return_new(
            ClOffset offset
            , const bool red
            , const ClauseStats& stats
        );
        ClOffset try_distill_clause_and_return_new_slow(
            ClOffset offset
            , const bool red
            , const ClauseStats& stats
        );
        bool distill_long_cls_all(vector<ClOffset>& offs, double time_mult);

        //Actual algorithms used
        bool distill_long_irred_cls();
        bool go_through_clauses(vector<ClOffset>& cls);
        Solver* solver;

        //For distill
        vector<Lit> lits;
        uint64_t oldBogoProps;
        int64_t maxNumProps;
        int64_t orig_maxNumProps;

        //Global status
        Stats runStats;
        Stats globalStats;
        size_t numCalls = 0;

};

inline const DistillerLong::Stats& DistillerLong::get_stats() const
{
    return globalStats;
}

} //end namespace

#endif //__DISTILLERALL_WITH_ALL_H__

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

#ifndef SUBSUMEIMPLICIT_H
#define SUBSUMEIMPLICIT_H

#include <vector>
#include "clause.h"
#include "constants.h"
#include "solvertypes.h"
#include "cloffset.h"
#include "watcharray.h"
#include "touchlist.h"

namespace CMSat {

using std::vector;

class Solver;
class Clause;

class SubsumeImplicit
{
public:
    explicit SubsumeImplicit(Solver* solver);
    void subsume_implicit(bool check_stats = true);
    uint32_t subsume_at_watch(const uint32_t at,
                              int64_t *timeAvail,
                              TouchList* touched = NULL);

    struct Stats {
        void clear()
        {
            *this = Stats();
        }
        Stats operator+=(const Stats& other);
        void print_short(const Solver* solver) const;
        void print() const;

        double time_used = 0.0;
        uint64_t numCalled = 0;
        uint64_t time_out = 0;
        uint64_t remBins = 0;
        uint64_t numWatchesLooked = 0;
    };
    Stats get_stats() const;
    double mem_used() const;

private:
    Solver* solver;
    int64_t timeAvailable;

    Lit lastLit2;
    Watched* lastBin;
    bool lastRed;
    vector<Lit> tmplits;
    Stats runStats;
    Stats globalStats;

    void clear()
    {
        lastLit2 = lit_Undef;
        lastBin = NULL;
        lastRed = false;
    }

    //ImplSubsumeData impl_subs_dat;
    void try_subsume_bin(
       const Lit lit
        , Watched* i
        , Watched*& j
        , int64_t* timeAvail
        , TouchList* touched = NULL
    );
};

} //end namespace

#endif //SUBSUMEIMPLICIT_H

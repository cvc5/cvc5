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

#include "str_impl_w_impl_stamp.h"
#include "clausecleaner.h"
#include "time_mem.h"
#include "solver.h"
#include "watchalgos.h"
#include "clauseallocator.h"
#include "sqlstats.h"

using namespace CMSat;

bool StrImplWImplStamp::str_impl_w_impl_stamp()
{
    #ifdef DEBUG_IMPLICIT_STATS
    solver->check_stats();
    #endif

    str_impl_data.clear();

    const size_t origTrailSize = solver->trail_size();
    timeAvailable =
        solver->conf.distill_implicit_with_implicit_time_limitM*1000LL*1000LL
        *solver->conf.global_timeout_multiplier;
    const int64_t orig_time = timeAvailable;
    double myTime = cpuTime();

    //Cannot handle empty
    if (solver->watches.size() == 0)
        return solver->okay();

    //Randomize starting point
    size_t upI = solver->mtrand.randInt(solver->watches.size()-1);
    size_t numDone = 0;
    for (; numDone < solver->watches.size() && timeAvailable > 0
        ; upI = (upI +1) % solver->watches.size(), numDone++

    ) {
        str_impl_data.numWatchesLooked++;
        const Lit lit = Lit::toLit(upI);
        distill_implicit_with_implicit_lit(lit);
    }

    //Enqueue delayed values
    if (!solver->fully_enqueue_these(str_impl_data.toEnqueue))
        goto end;

    //Add delayed binary clauses
    for(const BinaryClause& bin: str_impl_data.binsToAdd) {
        lits.clear();
        lits.push_back(bin.getLit1());
        lits.push_back(bin.getLit2());
        timeAvailable -= 5;
        solver->add_clause_int(lits, bin.isRed());
        if (!solver->okay())
            goto end;
    }

end:

    if (solver->conf.verbosity) {
        str_impl_data.print(
            solver->trail_size() - origTrailSize
            , cpuTime() - myTime
            , timeAvailable
            , orig_time
            , solver
        );
    }
    #ifdef DEBUG_IMPLICIT_STATS
    solver->check_stats();
    #endif

    return solver->okay();
}

void StrImplWImplStamp::distill_implicit_with_implicit_lit(const Lit lit)
{
    watch_subarray ws = solver->watches[lit];

    Watched* i = ws.begin();
    Watched* j = i;
    for (const Watched* end = ws.end()
        ; i != end
        ; i++
    ) {
        timeAvailable -= 2;
        if (timeAvailable < 0) {
            *j++ = *i;
            continue;
        }

        switch(i->getType()) {
            case CMSat::watch_clause_t:
                *j++ = *i;
                break;

            case CMSat::watch_binary_t:
                timeAvailable -= 20;
                strengthen_bin_with_bin(lit, i, j, end);
                break;

            default:
                assert(false);
                break;
        }
    }
    ws.shrink(i-j);
}

void StrImplWImplStamp::strengthen_bin_with_bin(
    const Lit lit
    , Watched* i
    , Watched*& j
    , const Watched* end
) {
    lits.clear();
    lits.push_back(lit);
    lits.push_back(i->lit2());
    if (solver->conf.doStamp) {
        timeAvailable -= 10;
        std::pair<size_t, size_t> tmp = solver->stamp.stampBasedLitRem(lits, STAMP_RED);
        str_impl_data.stampRem += tmp.first;
        str_impl_data.stampRem += tmp.second;
        assert(!lits.empty());
        if (lits.size() == 1) {
            str_impl_data.toEnqueue.push_back(lits[0]);
            (*solver->drat) << add << lits[0]
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;

            str_impl_data.remLitFromBin++;
            str_impl_data.stampRem++;
            *j++ = *i;
            return;
        }
    }

    //If inverted, then the inverse will never be found, because
    //watches are sorted
    if (i->lit2().sign()) {
        *j++ = *i;
        return;
    }

    //Try to look for a binary in this same watchlist
    //that has ~i->lit2() inside. Everything is sorted, so we are
    //lucky, this is speedy
    bool rem = false;
    const Watched* i2 = i;
    while(i2 != end
        && i2->isBin()
        && i->lit2().var() == i2->lit2().var()
    ) {
        timeAvailable -= 2;
        //Yay, we have found what we needed!
        if (i2->lit2() == ~i->lit2()) {
            rem = true;
            break;
        }

        i2++;
    }

    //Enqeue literal
    if (rem) {
        str_impl_data.remLitFromBin++;
        str_impl_data.toEnqueue.push_back(lit);
        (*solver->drat) << add << lit
        #ifdef STATS_NEEDED
        << solver->clauseID++
        << solver->sumConflicts
        #endif
        << fin;
    }
    *j++ = *i;
}

void StrImplWImplStamp::StrImplicitData::print(
    const size_t trail_diff
    , const double time_used
    , const int64_t timeAvailable
    , const int64_t orig_time
    , Solver* _solver
) const {
    bool time_out = timeAvailable <= 0;
    const double time_remain = float_div(timeAvailable, orig_time);

    cout
    << "c [impl str]"
    << " lit bin: " << remLitFromBin
    << " (by stamp: " << stampRem << ")"
    << " set-var: " << trail_diff
    << _solver->conf.print_times(time_used, time_out, time_remain)
    << " w-visit: " << numWatchesLooked
    << endl;

    if (_solver->sqlStats) {
        _solver->sqlStats->time_passed(
            _solver
            , "implicit str"
            , time_used
            , time_out
            , time_remain
        );
    }
}

double StrImplWImplStamp::mem_used() const
{
    double mem = sizeof(StrImplWImplStamp);
    mem += lits.size()*sizeof(Lit);

    return mem;

}

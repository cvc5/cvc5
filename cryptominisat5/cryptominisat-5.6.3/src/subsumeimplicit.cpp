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

#include "subsumeimplicit.h"
#include "clausecleaner.h"
#include "time_mem.h"
#include "solver.h"
#include "watchalgos.h"
#include "clauseallocator.h"
#include "sqlstats.h"

#include <cmath>
#include <iomanip>
using std::cout;
using std::endl;
using namespace CMSat;

SubsumeImplicit::SubsumeImplicit(Solver* _solver) :
    solver(_solver)
{
}

void SubsumeImplicit::try_subsume_bin(
    const Lit lit
    , Watched* i
    , Watched*& j
    , int64_t *timeAvail
    , TouchList* touched
) {
    //Subsume bin with bin
    if (i->lit2() == lastLit2) {
        //The sorting algorithm prefers irred to red, so it is
        //impossible to have irred before red
        assert(!(i->red() == false && lastRed == true));

        runStats.remBins++;
        assert(i->lit2().var() != lit.var());
        *timeAvail -= 30;
        *timeAvail -= solver->watches[i->lit2()].size();
        removeWBin(solver->watches, i->lit2(), lit, i->red());
        if (touched) {
            touched->touch(i->lit2());
        }
        if (i->red()) {
            solver->binTri.redBins--;
        } else {
            solver->binTri.irredBins--;
        }
        (*solver->drat) << del << lit << i->lit2() << fin;

        return;
    } else {
        lastBin = j;
        lastLit2 = i->lit2();
        lastRed = i->red();
        *j++ = *i;
    }
}

uint32_t SubsumeImplicit::subsume_at_watch(const uint32_t at,
                                           int64_t* timeAvail,
                                           TouchList* touched)
{
    runStats.numWatchesLooked++;
    const Lit lit = Lit::toLit(at);
    watch_subarray ws = solver->watches[lit];

    if (ws.size() > 1) {
        *timeAvail -= (int64_t)(ws.size()*std::ceil(std::log((double)ws.size())) + 20);
        std::sort(ws.begin(), ws.end(), WatchSorterBinTriLong());
    }
    /*cout << "---> Before" << endl;
    print_watch_list(ws, lit);*/

    Watched* i = ws.begin();
    Watched* j = i;
    clear();

    for (Watched* end = ws.end(); i != end; i++) {
        if (*timeAvail < 0) {
            *j++ = *i;
            continue;
        }

        switch(i->getType()) {
            case CMSat::watch_clause_t:
                *j++ = *i;
                break;

            case CMSat::watch_binary_t:
                try_subsume_bin(lit, i, j, timeAvail, touched);
                break;

            default:
                assert(false);
                break;
        }
    }
    ws.shrink(i-j);
    return i-j;
}

void SubsumeImplicit::subsume_implicit(const bool check_stats)
{
    assert(solver->okay());
    const double myTime = cpuTime();
    const uint64_t orig_timeAvailable =
        1000LL*1000LL*solver->conf.subsume_implicit_time_limitM
        *solver->conf.global_timeout_multiplier;
    timeAvailable = orig_timeAvailable;
    runStats.clear();

    //For randomization, we must have at least 1
    if (solver->watches.size() == 0) {
        return;
    }

    //Randomize starting point
    const size_t rnd_start = solver->mtrand.randInt(solver->watches.size()-1);
    size_t numDone = 0;
    for (;numDone < solver->watches.size() && timeAvailable > 0 && !solver->must_interrupt_asap()
         ;numDone++
    ) {
        const size_t at = (rnd_start + numDone)  % solver->watches.size();
        subsume_at_watch(at, &timeAvailable);
    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = (timeAvailable <= 0);
    const double time_remain = float_div(timeAvailable, orig_timeAvailable);
    runStats.numCalled++;
    runStats.time_used += time_used;
    runStats.time_out += time_out;
    if (solver->conf.verbosity) {
        runStats.print_short(solver);
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "subsume implicit"
            , time_used
            , time_out
            , time_remain
        );
    }

    if (check_stats) {
        #ifdef DEBUG_IMPLICIT_STATS
        solver->check_stats();
        #endif
    }

    globalStats += runStats;
}

SubsumeImplicit::Stats SubsumeImplicit::Stats::operator+=(const SubsumeImplicit::Stats& other)
{
    numCalled+= other.numCalled;
    time_out += other.time_out;
    time_used += other.time_used;
    remBins += other.remBins;
    numWatchesLooked += other.numWatchesLooked;

    return *this;
}

void SubsumeImplicit::Stats::print_short(const Solver* _solver) const
{
    cout
    << "c [impl sub]"
    << " bin: " << remBins
    << _solver->conf.print_times(time_used, time_out)
    << " w-visit: " << numWatchesLooked
    << endl;
}

void SubsumeImplicit::Stats::print() const
{
    cout << "c -------- IMPLICIT SUB STATS --------" << endl;
    print_stats_line("c time"
        , time_used
        , float_div(time_used, numCalled)
        , "per call"
    );

    print_stats_line("c timed out"
        , time_out
        , stats_line_percent(time_out, numCalled)
        , "% of calls"
    );

    print_stats_line("c rem bins"
        , remBins
    );
    cout << "c -------- IMPLICIT SUB STATS END --------" << endl;
}

SubsumeImplicit::Stats SubsumeImplicit::get_stats() const
{
    return globalStats;
}

double SubsumeImplicit::mem_used() const
{
    double mem = sizeof(SubsumeImplicit);
    mem += tmplits.size()*sizeof(Lit);

    return mem;
}

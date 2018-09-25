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

#ifndef __SEARCHSTATS_H__
#define __SEARCHSTATS_H__

#include <cstdint>

#include "solvertypes.h"
#include "clause.h"

namespace CMSat {

class SearchStats
{
public:
    void clear()
    {
        SearchStats tmp;
        *this = tmp;
    }

    SearchStats& operator+=(const SearchStats& other);
    SearchStats& operator-=(const SearchStats& other);
    SearchStats operator-(const SearchStats& other) const;
    void printCommon(uint64_t props, bool do_print_times) const;
    void print_short(uint64_t props, bool do_print_times) const;
    void print(uint64_t props, bool do_print_times) const;

    //Restart stats
    uint64_t blocked_restart = 0;
    uint64_t blocked_restart_same = 0;
    uint64_t numRestarts = 0;

    //Decisions
    uint64_t  decisions = 0;
    uint64_t  decisionsAssump = 0;
    uint64_t  decisionsRand = 0;
    uint64_t  decisionFlippedPolar = 0;

    //Clause shrinking
    uint64_t litsRedNonMin = 0;
    uint64_t litsRedFinal = 0;
    uint64_t recMinCl = 0;
    uint64_t recMinLitRem = 0;
    uint64_t permDiff_attempt = 0;
    uint64_t permDiff_success = 0;
    uint64_t permDiff_rem_lits = 0;

    uint64_t furtherShrinkAttempt = 0;
    uint64_t binTriShrinkedClause = 0;
    uint64_t cacheShrinkedClause = 0;
    uint64_t furtherShrinkedSuccess = 0;
    uint64_t stampShrinkAttempt = 0;
    uint64_t stampShrinkCl = 0;
    uint64_t stampShrinkLit = 0;
    uint64_t moreMinimLitsStart = 0;
    uint64_t moreMinimLitsEnd = 0;
    uint64_t recMinimCost = 0;

    //Learnt clause stats
    uint64_t learntUnits = 0;
    uint64_t learntBins = 0;
    uint64_t learntLongs = 0;
    uint64_t otfSubsumed = 0;
    uint64_t otfSubsumedImplicit = 0;
    uint64_t otfSubsumedLong = 0;
    uint64_t otfSubsumedRed = 0;
    uint64_t otfSubsumedLitsGained = 0;
    uint64_t cache_hit = 0;
    uint64_t red_cl_in_which0 = 0;

    //Hyper-bin & transitive reduction
    uint64_t advancedPropCalled = 0;
    uint64_t hyperBinAdded = 0;
    uint64_t transReduRemIrred = 0;
    uint64_t transReduRemRed = 0;

    //SolveFeatures
    uint64_t num_xors_found_last = 0;
    uint64_t num_gates_found_last = 0;
    uint64_t clauseID_at_start_inclusive = 0;
    uint64_t clauseID_at_end_exclusive = 0;

    //Resolution Stats
    AtecedentData<uint64_t> resolvs;

    //Stat structs
    ConflStats conflStats;

    //Time
    double cpu_time = 0.0;
};

}

#endif //__SEARCHSTATS_H__

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

#include "searchstats.h"

using namespace CMSat;

SearchStats& SearchStats::operator+=(const SearchStats& other)
{
    numRestarts += other.numRestarts;
    blocked_restart += other.blocked_restart;
    blocked_restart_same += other.blocked_restart_same;

    //Decisions
    decisions += other.decisions;
    decisionsAssump += other.decisionsAssump;
    decisionsRand += other.decisionsRand;
    decisionFlippedPolar += other.decisionFlippedPolar;

    //Conflict minimisation stats
    litsRedNonMin += other.litsRedNonMin;
    litsRedFinal += other.litsRedFinal;
    recMinCl += other.recMinCl;
    recMinLitRem += other.recMinLitRem;

    permDiff_attempt  += other.permDiff_attempt;
    permDiff_rem_lits += other.permDiff_rem_lits;
    permDiff_success += other.permDiff_success;

    furtherShrinkAttempt  += other.furtherShrinkAttempt;
    binTriShrinkedClause += other.binTriShrinkedClause;
    cacheShrinkedClause += other.cacheShrinkedClause;
    furtherShrinkedSuccess += other.furtherShrinkedSuccess;


    stampShrinkAttempt += other.stampShrinkAttempt;
    stampShrinkCl += other.stampShrinkCl;
    stampShrinkLit += other.stampShrinkLit;
    moreMinimLitsStart += other.moreMinimLitsStart;
    moreMinimLitsEnd += other.moreMinimLitsEnd;
    recMinimCost += other.recMinimCost;

    //Red stats
    learntUnits += other.learntUnits;
    learntBins += other.learntBins;
    learntLongs += other.learntLongs;
    otfSubsumed += other.otfSubsumed;
    otfSubsumedImplicit += other.otfSubsumedImplicit;
    otfSubsumedLong += other.otfSubsumedLong;
    otfSubsumedRed += other.otfSubsumedRed;
    otfSubsumedLitsGained += other.otfSubsumedLitsGained;
    cache_hit += other.cache_hit;
    red_cl_in_which0 += other.red_cl_in_which0;

    //Hyper-bin & transitive reduction
    advancedPropCalled += other.advancedPropCalled;
    hyperBinAdded += other.hyperBinAdded;
    transReduRemIrred += other.transReduRemIrred;
    transReduRemRed += other.transReduRemRed;

    //Stat structs
    resolvs += other.resolvs;
    conflStats += other.conflStats;

    //Time
    cpu_time += other.cpu_time;

    return *this;
}

SearchStats& SearchStats::operator-=(const SearchStats& other)
{
    numRestarts -= other.numRestarts;
    blocked_restart -= other.blocked_restart;
    blocked_restart_same -= other.blocked_restart_same;

    //Decisions
    decisions -= other.decisions;
    decisionsAssump -= other.decisionsAssump;
    decisionsRand -= other.decisionsRand;
    decisionFlippedPolar -= other.decisionFlippedPolar;

    //Conflict minimisation stats
    litsRedNonMin -= other.litsRedNonMin;
    litsRedFinal -= other.litsRedFinal;
    recMinCl -= other.recMinCl;
    recMinLitRem -= other.recMinLitRem;

    permDiff_attempt  -= other.permDiff_attempt;
    permDiff_rem_lits -= other.permDiff_rem_lits;
    permDiff_success -= other.permDiff_success;

    furtherShrinkAttempt  -= other.furtherShrinkAttempt;
    binTriShrinkedClause -= other.binTriShrinkedClause;
    cacheShrinkedClause -= other.cacheShrinkedClause;
    furtherShrinkedSuccess -= other.furtherShrinkedSuccess;

    stampShrinkAttempt -= other.stampShrinkAttempt;
    stampShrinkCl -= other.stampShrinkCl;
    stampShrinkLit -= other.stampShrinkLit;
    moreMinimLitsStart -= other.moreMinimLitsStart;
    moreMinimLitsEnd -= other.moreMinimLitsEnd;
    recMinimCost -= other.recMinimCost;

    //Red stats
    learntUnits -= other.learntUnits;
    learntBins -= other.learntBins;
    learntLongs -= other.learntLongs;
    otfSubsumed -= other.otfSubsumed;
    otfSubsumedImplicit -= other.otfSubsumedImplicit;
    otfSubsumedLong -= other.otfSubsumedLong;
    otfSubsumedRed -= other.otfSubsumedRed;
    otfSubsumedLitsGained -= other.otfSubsumedLitsGained;
    cache_hit -= other.cache_hit;
    red_cl_in_which0 -= other.red_cl_in_which0;

    //Hyper-bin & transitive reduction
    advancedPropCalled -= other.advancedPropCalled;
    hyperBinAdded -= other.hyperBinAdded;
    transReduRemIrred -= other.transReduRemIrred;
    transReduRemRed -= other.transReduRemRed;

    //Stat structs
    resolvs -= other.resolvs;
    conflStats -= other.conflStats;

    //Time
    cpu_time -= other.cpu_time;

    return *this;
}

SearchStats SearchStats::operator-(const SearchStats& other) const
{
    SearchStats result = *this;
    result -= other;
    return result;
}

void SearchStats::printCommon(uint64_t props, bool do_print_times) const
{
    print_stats_line("c restarts"
        , numRestarts
        , float_div(conflStats.numConflicts, numRestarts)
        , "confls per restart"

    );
    print_stats_line("c blocked restarts"
        , blocked_restart
        , float_div(blocked_restart, numRestarts)
        , "per normal restart"

    );
    if (do_print_times)
    print_stats_line("c time", cpu_time);
    print_stats_line("c decisions", decisions
        , stats_line_percent(decisionsRand, decisions)
        , "% random"
    );

    print_stats_line("c propagations", props);

    print_stats_line("c decisions/conflicts"
        , float_div(decisions, conflStats.numConflicts)
    );
}

void SearchStats::print_short(uint64_t props, bool do_print_times) const
{
    //Restarts stats
    printCommon(props, do_print_times);
    conflStats.print_short(cpu_time, do_print_times);

    print_stats_line("c conf lits non-minim"
        , litsRedNonMin
        , float_div(litsRedNonMin, conflStats.numConflicts)
        , "lit/confl"
    );

    print_stats_line("c conf lits final"
        , float_div(litsRedFinal, conflStats.numConflicts)
    );

    print_stats_line("c cache hit re-learnt cl"
        , cache_hit
        , stats_line_percent(cache_hit, conflStats.numConflicts)
        , "% of confl"
    );

    print_stats_line("c red which0"
        , red_cl_in_which0
        , stats_line_percent(red_cl_in_which0, conflStats.numConflicts)
        , "% of confl"
    );
}

void SearchStats::print(uint64_t props, bool do_print_times) const
{
    printCommon(props, do_print_times);
    conflStats.print(cpu_time, do_print_times);

    /*assert(numConflicts
        == conflsBin + conflsTri + conflsLongIrred + conflsLongRed);*/

    cout << "c LEARNT stats" << endl;
    print_stats_line("c units learnt"
        , learntUnits
        , stats_line_percent(learntUnits, conflStats.numConflicts)
        , "% of conflicts");

    print_stats_line("c bins learnt"
        , learntBins
        , stats_line_percent(learntBins, conflStats.numConflicts)
        , "% of conflicts");

    print_stats_line("c long learnt"
        , learntLongs
        , stats_line_percent(learntLongs, conflStats.numConflicts)
        , "% of conflicts"
    );

    print_stats_line("c otf-subs"
        , otfSubsumed
        , ratio_for_stat(otfSubsumed, conflStats.numConflicts)
        , "/conflict"
    );

    print_stats_line("c otf-subs implicit"
        , otfSubsumedImplicit
        , stats_line_percent(otfSubsumedImplicit, otfSubsumed)
        , "%"
    );

    print_stats_line("c otf-subs long"
        , otfSubsumedLong
        , stats_line_percent(otfSubsumedLong, otfSubsumed)
        , "%"
    );

    print_stats_line("c otf-subs learnt"
        , otfSubsumedRed
        , stats_line_percent(otfSubsumedRed, otfSubsumed)
        , "% otf subsumptions"
    );

    print_stats_line("c otf-subs lits gained"
        , otfSubsumedLitsGained
        , ratio_for_stat(otfSubsumedLitsGained, otfSubsumed)
        , "lits/otf subsume"
    );

    print_stats_line("c cache hit re-learnt cl"
        , cache_hit
        , stats_line_percent(cache_hit, conflStats.numConflicts)
        , "% of confl"
    );

    print_stats_line("c red which0"
        , red_cl_in_which0
        , stats_line_percent(red_cl_in_which0, conflStats.numConflicts)
        , "% of confl"
    );

    cout << "c SEAMLESS HYPERBIN&TRANS-RED stats" << endl;
    print_stats_line("c advProp called"
        , advancedPropCalled
    );
    print_stats_line("c hyper-bin add bin"
        , hyperBinAdded
        , ratio_for_stat(hyperBinAdded, advancedPropCalled)
        , "bin/call"
    );
    print_stats_line("c trans-red rem irred bin"
        , transReduRemIrred
        , ratio_for_stat(transReduRemIrred, advancedPropCalled)
        , "bin/call"
    );
    print_stats_line("c trans-red rem red bin"
        , transReduRemRed
        , ratio_for_stat(transReduRemRed, advancedPropCalled)
        , "bin/call"
    );

    cout << "c CONFL LITS stats" << endl;
    print_stats_line("c orig "
        , litsRedNonMin
        , ratio_for_stat(litsRedNonMin, conflStats.numConflicts)
        , "lit/confl"
    );

    print_stats_line("c recurs-min effective"
        , recMinCl
        , stats_line_percent(recMinCl, conflStats.numConflicts)
        , "% attempt successful"
    );

    print_stats_line("c recurs-min lits"
        , recMinLitRem
        , stats_line_percent(recMinLitRem, litsRedNonMin)
        , "% less overall"
    );

    print_stats_line("c permDiff call%"
        , stats_line_percent(permDiff_attempt, conflStats.numConflicts)
        , stats_line_percent(permDiff_success, permDiff_attempt)
        , "% attempt successful"
    );

    print_stats_line("c permDiff lits-rem"
        , permDiff_rem_lits
        , ratio_for_stat(permDiff_rem_lits, permDiff_attempt)
        , "less lits/cl on attempts"
     );


    print_stats_line("c further-min call%"
        , stats_line_percent(furtherShrinkAttempt, conflStats.numConflicts)
        , stats_line_percent(furtherShrinkedSuccess, furtherShrinkAttempt)
        , "% attempt successful"
    );

    print_stats_line("c bintri-min lits"
        , binTriShrinkedClause
        , stats_line_percent(binTriShrinkedClause, litsRedNonMin)
        , "% less overall"
    );

    print_stats_line("c cache-min lits"
        , cacheShrinkedClause
        , stats_line_percent(cacheShrinkedClause, litsRedNonMin)
        , "% less overall"
    );

    print_stats_line("c stamp-min call%"
        , stats_line_percent(stampShrinkAttempt, conflStats.numConflicts)
        , stats_line_percent(stampShrinkCl, stampShrinkAttempt)
        , "% attempt successful"
    );

    print_stats_line("c stamp-min lits"
        , stampShrinkLit
        , stats_line_percent(stampShrinkLit, litsRedNonMin)
        , "% less overall"
    );

    print_stats_line("c final avg"
        , ratio_for_stat(litsRedFinal, conflStats.numConflicts)
    );

    //General stats
    //print_stats_line("c Memory used", (double)mem_used / 1048576.0, " MB");
    #if !defined(_MSC_VER) && defined(RUSAGE_THREAD)
    print_stats_line("c single-thread CPU time", cpu_time, " s");
    #else
    print_stats_line("c all-threads sum CPU time", cpu_time, " s");
    #endif
}

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


#include "prober.h"

#include <iomanip>
#include <utility>
#include <set>
#include <utility>
#include <cmath>

#include "solver.h"
#include "clausecleaner.h"
#include "time_mem.h"
#include "clausecleaner.h"
#include "completedetachreattacher.h"
#include "sqlstats.h"

using namespace CMSat;
using std::make_pair;
using std::set;
using std::cout;
using std::endl;

//#define VERBOSE_DEUBUG

/**
@brief Sets up variables that are used between calls to probe()
*/
Prober::Prober(Solver* _solver):
    solver(_solver)
    , numPropsMultiplier(1.0)
    , lastTimeZeroDepthAssings(0)
{
}

uint64_t Prober::limit_used() const
{
    return solver->propStats.bogoProps
        + solver->propStats.otfHyperTime
        + extraTime
        + extraTimeCache;
}

void Prober::checkOTFRatio()
{
    double ratio = float_div(solver->propStats.bogoProps,
        solver->propStats.otfHyperTime + solver->propStats.bogoProps);

    /*static int val = 0;
    if (val  % 10 == 0) {
        cout << "Ratio is " << std::setprecision(2) << ratio << endl;
    }
    val++;*/

    if (solver->conf.verbosity) {
        cout
        << "c [probe] Ratio of hyperbin/(bogo+hyperbin) is : "
        << std::setprecision(2) << ratio
        << " (this indicates how much time is spent doing hyperbin&trans-red)"
        << endl;
    }

    const uint64_t time_limit =
        solver->conf.otf_hyper_time_limitM*1000ULL*1000ULL
        *solver->conf.global_timeout_multiplier;
    if (solver->propStats.bogoProps+solver->propStats.otfHyperTime
            > time_limit
        && ratio < solver->conf.otf_hyper_ratio_limit
        && solver->conf.otfHyperbin
        && !(solver->drat->enabled() || solver->conf.simulate_drat)
    ) {
        solver->conf.otfHyperbin = false;
        if (solver->conf.verbosity) {
            cout << "c [probe] no longer doing OTF hyper-bin&trans-red" << endl;
        }
        solver->needToAddBinClause.clear();
        solver->uselessBin.clear();
    }
}

void Prober::reset_stats_and_state()
{
    extraTime = 0;
    extraTimeCache = 0;
    solver->propStats.clear();
    runStats.clear();
    runStats.origNumBins = solver->binTri.redBins + solver->binTri.irredBins;

    visitedAlready.clear();
    visitedAlready.resize(solver->nVars()*2, 0);
    propagatedBitSet.clear();
    propagated.clear();
    propagated.resize(solver->nVars(), 0);
    propValue.resize(solver->nVars());
}

uint64_t Prober::calc_num_props_limit()
{
    uint64_t num_props_limit = solver->conf.probe_bogoprops_time_limitM
        *solver->conf.global_timeout_multiplier
        *1000ULL*1000ULL;

    //Bogoprops for hyper-bin is MUCH more precise, so if no propagateFull???
    //then mush less bogoProps will lead to the same amount of time
    if (!solver->conf.otfHyperbin) {
        num_props_limit /= 4;
    }

    //Account for cache being too small
    const size_t num_active_vars = solver->num_active_vars();
    if (num_active_vars < 50LL*1000LL) {
        num_props_limit *= 1.2;
    }
    if (solver->litStats.redLits + solver->litStats.irredLits  < 2LL*1000LL*1000LL) {
        num_props_limit *= 1.2;
    }
    if (num_active_vars > 600LL*1000LL) {
        num_props_limit *= 0.8;
    }
    if (solver->litStats.redLits + solver->litStats.irredLits > 20LL*1000LL*1000LL) {
        num_props_limit *= 0.8;
    }

    runStats.origNumFreeVars = num_active_vars;
    if (solver->conf.verbosity) {
    cout
        << "c [probe] lits : "
        << std::setprecision(2) << (double)(solver->litStats.redLits + solver->litStats.irredLits)/(1000.0*1000.0)
        << "M"
        << " act vars: "
        << std::setprecision(2) << (double)num_active_vars/1000.0 << "K"
        << " BP+HP todo: "
        << std::setprecision(2) << (double)num_props_limit/(1000.0*1000.0) << "M"
        << endl;
    }

    return num_props_limit;
}

void Prober::clean_clauses_before_probe()
{
    if (solver->conf.verbosity >= 6) {
        cout << "c Cleaning clauses before probing." << endl;
    }
    solver->clauseCleaner->remove_and_clean_all();
    if (solver->conf.verbosity >= 6) {
        cout << "c Cleaning clauses before probing finished." << endl;
    }
}

uint64_t Prober::update_num_props_limit_based_on_prev_perf(uint64_t num_props_limit)
{
     //If failed var searching is going good, do successively more and more of it
    const double percentEffectLast =
        float_div(lastTimeZeroDepthAssings, runStats.origNumFreeVars)
        * 100.0;

    if (percentEffectLast > 20.0) {
        //It's doing VERY well
        numPropsMultiplier = std::min(numPropsMultiplier*2, 5.0);
    } else if (percentEffectLast >= 10.0) {
        //It's doing well
        numPropsMultiplier = std::min(numPropsMultiplier*1.6, 4.0);
    } else if (percentEffectLast <= 3) {
        //It's doing badly
        numPropsMultiplier = 0.5;
    } else {
        //It's doing OK
        numPropsMultiplier = 1.0;
    }

    //First start is special, there is no previous record
    if (globalStats.numCalls == 0) {
        numPropsMultiplier = 1.0;
    }

    num_props_limit = (double)num_props_limit * numPropsMultiplier;
    const size_t num_props_limitAftPerf = num_props_limit;
    num_props_limit = (double)num_props_limit * std::pow((double)(globalStats.numCalls+1), 0.3);

    if (solver->conf.verbosity >=2 ) {
        cout
        << "c [probe] NumProps after perf multi: "
        << std::setprecision(2) << (double)num_props_limitAftPerf/(1000.0*1000.0)
        << "M"
        << " after numcall multi: "
        << std::setprecision(2) << (double)num_props_limit/(1000.0*1000.0)
        << "M (<- final)"
        << endl;
    }

    return num_props_limit;
}

void Prober::clean_clauses_after_probe()
{
    double time = cpuTime();
    bool advancedCleanup = false;

    //If more than 10% were set, detach&reattach. It's faster
    if ((double)runStats.origNumFreeVars - (double)solver->get_num_free_vars()
            >  (double)runStats.origNumFreeVars/10.0
        && solver->getNumLongClauses() > 200000
    ) {
        if (solver->conf.verbosity >= 5)
            cout << "c Advanced cleanup after probing" << endl;

        advancedCleanup = true;
        CompleteDetachReatacher reattacher(solver);
        reattacher.detach_nonbins_nontris();
        const bool ret = reattacher.reattachLongs();
        release_assert(ret == true);
    } else {
        if (solver->conf.verbosity >= 5)
            cout << "c Standard cleanup after probing" << endl;

        solver->clauseCleaner->remove_and_clean_all();
    }

    if (solver->conf.verbosity  >= 1 &&
        (runStats.zeroDepthAssigns > 100 || advancedCleanup)
    ) {
        double time_used = cpuTime() - time;
        cout
        << "c [probe] cleaning up after"
        << solver->conf.print_times(time_used)
        << endl;
    }
}

void Prober::check_if_must_disable_otf_hyperbin_and_tred(const uint64_t num_props_limit)
{
    const double ratioUsedTime = float_div(
        solver->propStats.bogoProps + solver->propStats.otfHyperTime + extraTime
        , num_props_limit);
    if (solver->conf.otfHyperbin
        //Visited less than half
        && float_div(runStats.numVisited, runStats.origNumFreeVars) < 0.8
        //And we used up most of the time
        && ratioUsedTime > 0.8
    ) {
        checkOTFRatio();
    }
}

void Prober::check_if_must_disable_cache_update()
{
    //If time wasted on cache updating (extraTime) is large, stop cache
    //updation
    double timeOnCache = float_div(extraTimeCache
        , solver->propStats.bogoProps
            + solver->propStats.otfHyperTime
            + extraTime + extraTimeCache
    ) ;


    //More than 50% of the time is spent updating the cache... that's a lot
    //Disable and free
    if (timeOnCache > 50.0 && solver->conf.doCache)  {
        if (solver->conf.verbosity) {
            cout
            << "c [probe] too much time spent on updating cache: "
            << std::fixed << std::setprecision(1) << timeOnCache
            << "% during probing --> disabling cache"
            << endl;
        }

        solver->conf.doCache = false;
        solver->implCache.free();
    } else {
        if (solver->conf.verbosity) {
            cout
            << "c [probe] time spent updating cache during probing: "
            << std::fixed << std::setprecision(1) << timeOnCache
            << "%"
            << endl;
        }
    }
}

vector<uint32_t> Prober::randomize_possible_choices()
{
    vars_to_probe.clear();
    for(size_t i = 0; i < solver->nVars(); i++) {
        if (solver->value(i) == l_Undef
            && solver->varData[i].removed == Removed::none
        ) {
            vars_to_probe.push_back(i);
        }
    }

    //Random swap
    for (size_t i = 0
        ; i + 1< vars_to_probe.size()
        ; i++
    ) {
        std::swap(
            vars_to_probe[i]
            , vars_to_probe[i+solver->mtrand.randInt(vars_to_probe.size()-1-i)]
        );
    }

    return vars_to_probe;
}

bool Prober::probe(vector<uint32_t>* probe_order)
{
    assert(solver->ok);
    assert(solver->qhead == solver->trail.size());
    assert(solver->decisionLevel() == 0);
    assert(solver->nVars() > 0);

    clean_clauses_before_probe();
    reset_stats_and_state();
    uint64_t num_props_limit = calc_num_props_limit();

    const double myTime = cpuTime();
    const size_t origTrailSize = solver->trail_size();
    num_props_limit = update_num_props_limit_based_on_prev_perf(num_props_limit);

    if (probe_order == NULL) {
        randomize_possible_choices();
    } else {
        vars_to_probe = *probe_order;
    }

    if (solver->conf.verbosity >= 10) {
        cout << "Order of probe:";
        for(auto x: vars_to_probe) {
            cout << x+1 << ", ";
        }
        cout << endl;
    }

    assert(solver->propStats.bogoProps == 0);
    assert(solver->propStats.otfHyperTime == 0);
    single_prop_tout = (double)num_props_limit *solver->conf.single_probe_time_limit_perc;

    for(size_t i = 0
        ; i < vars_to_probe.size()
        && limit_used() < num_props_limit
        && !solver->must_interrupt_asap()
        ; i++
    ) {
        if ((i & 0xff) == 0xff
            && cpuTime() >= solver->conf.maxTime
        ) {
            break;
        }
        extraTime += 20;
        runStats.numLoopIters++;
        const uint32_t var = vars_to_probe[i];

        //Probe 'false' first --> this is not critical
        Lit lit = Lit(var, false);

        //Check if var is set already
        if (solver->value(lit.var()) != l_Undef
            || solver->varData[lit.var()].removed != Removed::none
            || visitedAlready[lit.toInt()]
        ) {
            continue;
        }

        runStats.numVarProbed++;
        extraTime += 20;

        if (!try_this(lit, true))
            goto end;

        if (solver->value(lit) == l_Undef
            && !try_this(~lit, false)
        ) {
            goto end;
        }
    }

end:

    if (solver->conf.verbosity >= 10) {
        cout << "c main loop for " << __func__
        << " finished: "
        << " must_interrupt? " << solver->must_interrupt_asap()
        << " limit_used? " << (limit_used() >= num_props_limit)
        << endl;
    }

    //Delete any remaining binaries to add or remove
    //next time, variables will be renumbered/etc. so it will be wrong
    //to add/remove them
    solver->needToAddBinClause.clear();
    solver->uselessBin.clear();

    runStats.zeroDepthAssigns = solver->trail_size() - origTrailSize;
    if (solver->ok && runStats.zeroDepthAssigns) {
        clean_clauses_after_probe();
    }

    update_and_print_stats(myTime, num_props_limit);
    check_if_must_disable_otf_hyperbin_and_tred(num_props_limit);
    check_if_must_disable_cache_update();

    return solver->okay();
}

void Prober::update_and_print_stats(const double myTime, const uint64_t num_props_limit)
{
    for(size_t i = 0; i < visitedAlready.size(); i++) {
        if (visitedAlready[i])
            runStats.numVisited++;
    }
    lastTimeZeroDepthAssings = runStats.zeroDepthAssigns;
    const double time_used = cpuTime() - myTime;
    const bool time_out = (limit_used() > num_props_limit);
    const double time_remain = float_div((int64_t)num_props_limit-(int64_t)limit_used(), num_props_limit);
    runStats.cpu_time = time_used;
    runStats.propStats = solver->propStats;
    runStats.timeAllocated += num_props_limit;
    runStats.numCalls = 1;
    globalStats += runStats;

    if (solver->conf.verbosity) {
        if (solver->conf.verbosity >= 3)
            runStats.print(solver->nVars(), solver->conf.do_print_times);
        else
            runStats.print_short(solver, time_out, time_remain);
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "probe"
            , time_used
            , time_out
            , time_remain
        );
    }
}

void Prober::clear_up_before_first_set()
{
    extraTime += propagatedBitSet.size();
    for(size_t varset: propagatedBitSet) {
        propagated[varset] = false;
    }
    propagatedBitSet.clear();
}

void Prober::update_cache(Lit thisLit, Lit lit, size_t numElemsSet)
{
    //Update cache, if the trail was within limits (cacheUpdateCutoff)
    const Lit ancestor = solver->varData[thisLit.var()].reason.getAncestor();
    if (solver->conf.doCache
        && thisLit != lit
        && numElemsSet <= solver->conf.cacheUpdateCutoff
        //&& cacheUpdated[(~ancestor).toInt()] == 0
    ) {
        //Update stats/markings
        //cacheUpdated[(~ancestor).toInt()]++;
        extraTime += 1;
        extraTimeCache += solver->implCache[~ancestor].lits.size()/30;
        extraTimeCache += solver->implCache[~thisLit].lits.size()/30;

        const bool redStep = solver->varData[thisLit.var()].reason.isRedStep();

        //Update the cache now
        assert(ancestor != lit_Undef);
        bool taut = solver->implCache[~ancestor].merge(
            solver->implCache[~thisLit].lits
            , thisLit
            , redStep
            , ancestor.var()
            , solver->seen
        );

        //If tautology according to cache we can
        //enqueue ~ancestor at toplevel since both
        //~ancestor V OTHER, and ~ancestor V ~OTHER are technically in
        if (taut
            && solver->varData[ancestor.var()].removed == Removed::none
        ) {
            toEnqueue.push_back(~ancestor);
            (*solver->drat) << add << ~ancestor
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;
            if (solver->conf.verbosity >= 10)
                cout << "c Tautology from cache indicated we can enqueue " << (~ancestor) << endl;
        }

        #ifdef VERBOSE_DEBUG_FULLPROP
        cout << "The impl cache of " << (~ancestor) << " is now: ";
        cout << solver->implCache[(~ancestor).toInt()] << endl;
        #endif
    }
}

void Prober::check_and_set_both_prop(Lit probed_lit, uint32_t var, bool first)
{
    //If this is the first, set what is propagated
    if (first) {
        //Visited this var, needs clear later on
        propagatedBitSet.push_back(var);

        //Set prop has been done
        propagated[var] = true;

        //Set propValue
        if (solver->value(var) == l_True)
            propValue[var] = true;
        else
            propValue[var] = false;
    } else if (propagated[var]) {
        if (propValue[var] == (solver->value(var) == l_True)) {

            //they both imply the same
            const Lit litToEnq = Lit(var, !propValue[var]);
            toEnqueue.push_back(litToEnq);
            (*solver->drat) << add << probed_lit << litToEnq
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;
            (*solver->drat) << add << ~probed_lit << litToEnq
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;
            (*solver->drat) << add << litToEnq
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;

            if (solver->conf.verbosity >= 10)
                cout << "c Bothprop indicated to enqueue " << litToEnq << endl;
        }
    }
}

void Prober::add_rest_of_lits_to_cache(Lit lit)
{
    tmp_lits.clear();
    for (int64_t c = solver->trail_size()-1
        ; c != (int64_t)solver->trail_lim[0] - 1
        ; c--
    ) {
        extraTime += 2;
        const Lit thisLit = solver->trail[c];
        tmp_lits.push_back(thisLit);
    }

    bool taut = solver->implCache[~lit].merge(
        tmp_lits
        , lit_Undef
        , true //Red step -- we don't know, so we assume
        , lit.var()
        , solver->seen
    );

    //If tautology according to cache we can
    //enqueue ~lit at toplevel since both
    //~lit V OTHER, and ~lit V ~OTHER are technically in
    if (taut) {
        toEnqueue.push_back(~lit);
        (*solver->drat) << add << ~lit
        #ifdef STATS_NEEDED
        << solver->clauseID++
        << solver->sumConflicts
        #endif
        << fin;
    }
}

bool Prober::check_timeout_due_to_hyperbin()
{
    //If we timed out on ONE call, turn otf hyper-bin off
    //and return --> the "visitedAlready" will be wrong
    if (solver->timedOutPropagateFull
        && !(solver->drat->enabled() || solver->conf.simulate_drat)
    ) {
        if (solver->conf.verbosity) {
            cout
            << "c [probe] intra-propagation timout,"
            << " turning off OTF hyper-bin&trans-red"
            << endl;
        }

        solver->conf.otfHyperbin = false;
        solver->cancelUntil<false, true>(0);

        runStats.addedBin += solver->hyper_bin_res_all();
        std::pair<size_t, size_t> tmp = solver->remove_useless_bins();
        runStats.removedIrredBin += tmp.first;
        runStats.removedRedBin += tmp.second;

        for(vector<uint32_t>::const_iterator
            it = propagatedBitSet.begin(), end = propagatedBitSet.end()
            ; it != end
            ; ++it
        ) {
            propagated[*it] = false;
        }
        propagatedBitSet.clear();
        toEnqueue.clear();
        return true;
    }

    return false;
}

bool Prober::try_this(const Lit lit, const bool first)
{
    //Clean state if this is the 1st of two
    if (first) {
        clear_up_before_first_set();
    }
    toEnqueue.clear();
    runStats.numProbed++;
    solver->new_decision_level();
    solver->enqueue(lit);
    solver->depth[lit.var()] = 0;
    if (solver->conf.verbosity >= 6) {
        cout
        << "c Probing lit " << lit
        << endl;
    }

    Lit failed = lit_Undef;
    if (!propagate(failed)) {
        return solver->okay();
    }

    if (failed == lit_Undef) {
        if (solver->conf.verbosity >= 6)
            cout << "c Did not fail on lit " << lit << endl;

        //Fill bothprop, cache
        assert(solver->decisionLevel() > 0);
        size_t numElemsSet = solver->trail_size() - solver->trail_lim[0];
        for (int64_t c = solver->trail_size()-1
            ; c != (int64_t)solver->trail_lim[0] - 1
            ; c--
        ) {
            extraTime += 2;
            const Lit thisLit = solver->trail[c];
            const uint32_t var = thisLit.var();

            if (solver->conf.doBothProp) {
                check_and_set_both_prop(lit, var, first);
            }
            visitedAlready[thisLit.toInt()] = 1;
            if (solver->conf.otfHyperbin) {
                update_cache(thisLit, lit, numElemsSet);
            }
        }

        if (!solver->conf.otfHyperbin
            && solver->conf.doCache
        ) {
            add_rest_of_lits_to_cache(lit);
        }
    }

    solver->cancelUntil<false, true>(0);
    solver->add_otf_subsume_long_clauses();
    solver->add_otf_subsume_implicit_clause();
    runStats.addedBin += solver->hyper_bin_res_all();
    std::pair<size_t, size_t> tmp = solver->remove_useless_bins();
    runStats.removedIrredBin += tmp.first;
    runStats.removedRedBin += tmp.second;

    if (failed != lit_Undef) {
        if (solver->conf.verbosity >= 6) {
            cout << "c Failed while enq + prop " << lit
            << " Lit that got propagated to both values: " << failed << endl;
        }
        runStats.numFailed++;
        #ifdef STATS_NEEDED
        runStats.conflStats.update(solver->lastConflictCausedBy);
        #endif
        runStats.conflStats.numConflicts++;

        vector<Lit> lits;
        lits.push_back(~failed);
        solver->add_clause_int(lits, true);
        clear_up_before_first_set();
        return solver->okay();
    } else {
        assert(solver->ok);
        runStats.bothSameAdded += toEnqueue.size();
        extraTime += 3*toEnqueue.size();
        return solver->fully_enqueue_these(toEnqueue);
    }
}

bool Prober::propagate(Lit& failed)
{
    if (solver->conf.otfHyperbin) {
        //Set timeout for ONE enqueue. This used so that in case ONE enqueue
        //takes too long (usually because of hyper-bin), we exit early
        uint64_t timeout = std::numeric_limits<uint64_t>::max();
        if (!(solver->drat->enabled() || solver->conf.simulate_drat)) {
            timeout = solver->propStats.otfHyperTime
            + solver->propStats.bogoProps
            + single_prop_tout;
        }

        //DFS is expensive, actually. So do BFS 50% of the time
        if (solver->conf.doStamp &&
            (force_stamp >= 1 || (solver->mtrand.randInt(1) == 0 && force_stamp == -1))
        ) {
            StampType stampType;
            if (force_stamp == 2) {
                stampType = StampType::STAMP_IRRED;
            } else if (force_stamp == 1) {
                stampType = StampType::STAMP_RED;
            } else {
                stampType = solver->mtrand.randInt(1) ? StampType::STAMP_IRRED : StampType::STAMP_RED;
            }
            failed = solver->propagate_dfs(stampType, timeout);
        } else {
            failed = solver->propagate_bfs(timeout);
        }

        if (check_timeout_due_to_hyperbin()) {
            return false;
        }
    } else {
        //No hyper-bin so we use regular propagate and regular analyze

        PropBy confl = solver->propagate<true>();
        if (!confl.isNULL()) {
            uint32_t  glue;
            uint32_t  backtrack_level;
            solver->analyze_conflict<true>(
                confl
                , backtrack_level  //return backtrack level here
                , glue             //return glue here
            );
            if (solver->learnt_clause.empty()) {
                solver->ok = false;
                return false;
            }
            assert(solver->learnt_clause.size() == 1);
            failed = ~(solver->learnt_clause[0]);
        }
    }

    return true;
}

size_t Prober::mem_used() const
{
    size_t mem = 0;
    mem += visitedAlready.capacity()*sizeof(char);
    mem += propagatedBitSet.capacity()*sizeof(uint32_t);
    mem += toEnqueue.capacity()*sizeof(Lit);
    mem += tmp_lits.capacity()*sizeof(Lit);
    mem += propagated.capacity()/8;
    mem += propValue.capacity()/8;

    return mem;
}

// void Prober::fillToTry(vector<uint32_t>& toTry)
// {
//     uint32_t max = std::min(solver->negPosDist.size()-1, (size_t)300);
//     while(true) {
//         uint32_t var = solver->negPosDist[solver->mtrand.randInt(max)].var;
//         if (solver->value(var) != l_Undef
//             || (solver->varData[var].removed != Removed::none)
//         ) continue;
//
//         bool OK = true;
//         for (uint32_t i = 0; i < toTry.size(); i++) {
//             if (toTry[i] == var) {
//                 OK = false;
//                 break;
//             }
//         }
//         if (OK) {
//             toTry.push_back(var);
//             return;
//         }
//     }
// }
//
// const bool Prober::tryMultiLevelAll()
// {
//     assert(solver->ok);
//     uint32_t backupNumUnits = solver->trail_size();
//     double myTime = cpuTime();
//     uint32_t numTries = 0;
//     uint32_t finished = 0;
//     uint64_t oldBogoProps = solver->bogoProps;
//     uint32_t enqueued = 0;
//     uint32_t numFailed = 0;
//
//     if (solver->negPosDist.size() < 30) return true;
//
//     propagated.resize(solver->nVars(), 0);
//     propagated2.resize(solver->nVars(), 0);
//     propValue.resize(solver->nVars(), 0);
//     assert(propagated.isZero());
//     assert(propagated2.isZero());
//
//     vector<uint32_t> toTry;
//     while(solver->bogoProps < oldBogoProps + 300*1000*1000) {
//         toTry.clear();
//         for (uint32_t i = 0; i < 3; i++) {
//             fillToTry(toTry);
//         }
//         numTries++;
//         if (!tryMultiLevel(toTry, enqueued, finished, numFailed)) goto end;
//     }
//
//     end:
//     assert(propagated.isZero());
//     assert(propagated2.isZero());
//
//     cout
//     << "c multiLevelBoth tried " <<  numTries
//     << " finished: " << finished
//     << " units: " << (solver->trail_size() - backupNumUnits)
//     << " enqueued: " << enqueued
//     << " numFailed: " << numFailed
//     << " time: " << (cpuTime() - myTime)
//     << endl;
//
//     return solver->okay();
// }
//
// const bool Prober::tryMultiLevel(const vector<uint32_t>& vars, uint32_t& enqueued, uint32_t& finished, uint32_t& numFailed)
// {
//     assert(solver->ok);
//
//     vector<Lit> toEnqueue;
//     bool first = true;
//     bool last = false;
//     //cout << "//////////////////" << endl;
//     for (uint32_t comb = 0; comb < (1U << vars.size()); comb++) {
//         last = (comb == (1U << vars.size())-1);
//         solver->new_decision_level();
//         for (uint32_t i = 0; i < vars.size(); i++) {
//             solver->enqueue(Lit(vars[i], comb&(0x1 << i)));
//             //cout << "lit: " << Lit(vars[i], comb&(1U << i)) << endl;
//         }
//         //cout << "---" << endl;
//         bool failed = !(solver->propagate().isNULL());
//         if (failed) {
//             solver->cancelUntil<false>(0);
//             if (!first) propagated.setZero();
//             numFailed++;
//             return true;
//         }
//
//         for (int sublevel = solver->trail_size()-1; sublevel > (int)solver->trail_lim[0]; sublevel--) {
//             uint32_t x = solver->trail[sublevel].var();
//             if (first) {
//                 propagated.setBit(x);
//                 if (solver->assigns[x].getBool()) propValue.setBit(x);
//                 else propValue.clearBit(x);
//             } else if (last) {
//                 if (propagated[x] && solver->assigns[x].getBool() == propValue[x])
//                     toEnqueue.push_back(Lit(x, !propValue[x]));
//             } else {
//                 if (solver->assigns[x].getBool() == propValue[x]) {
//                     propagated2.setBit(x);
//                 }
//             }
//         }
//         solver->cancelUntil<false>(0);
//         if (!first && !last) propagated &= propagated2;
//         propagated2.setZero();
//         if (propagated.isZero()) return true;
//         first = false;
//     }
//     propagated.setZero();
//     finished++;
//
//     for (vector<Lit>::iterator l = toEnqueue.begin(), end = toEnqueue.end(); l != end; l++) {
//         enqueued++;
//         solver->enqueue(*l);
//     }
//     solver->ok = solver->propagate().isNULL();
//     //std::exit(-1);
//
//     return solver->okay();
// }

void Prober::Stats::print_short(const Solver* solver, const bool time_out, const double time_remain) const
{
    cout
    << "c [probe]"
    << " 0-depth assigns: " << zeroDepthAssigns
    << " bsame: " << bothSameAdded
    << " Flit: " << numFailed

    // x2 because it's LITERAL visit
    << " Visited: " << numVisited << "/" << (origNumFreeVars*2)
    << "(" << std::setprecision(1)
    << stats_line_percent(numVisited, origNumFreeVars*2)
    << "%)"
    << endl;

    cout
    << "c [probe]"
    << " probed: " << numProbed
    << "(" << std::setprecision(1)
    // x2 because it's LITERAL probed
    << stats_line_percent(numProbed, origNumFreeVars*2)
    << "%)"

    << " hyperBin:" << addedBin
    << " transR-Irred:" << removedIrredBin
    << " transR-Red:" << removedRedBin
    << endl;

    cout
    << "c [probe]"
    << " BP: " << std::fixed << std::setprecision(1)
    << (double)(propStats.bogoProps)/1000000.0  << "M"
    << " HP: " << std::fixed << std::setprecision(1)
    << (double)(propStats.otfHyperTime)/1000000.0  << "M"

    << solver->conf.print_times(cpu_time, time_out, time_remain)
    << endl;
}

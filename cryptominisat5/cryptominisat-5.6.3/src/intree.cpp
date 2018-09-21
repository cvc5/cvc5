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

#include "intree.h"
#include "solver.h"
#include "varreplacer.h"
#include "clausecleaner.h"
#include "sqlstats.h"
#include "watchalgos.h"

#include <cmath>
#include <cassert>

using namespace CMSat;

InTree::InTree(Solver* _solver) :
    solver(_solver)
    , seen(_solver->seen)
{}

bool InTree::replace_until_fixedpoint(bool& aborted)
{
    uint64_t time_limit =
        solver->conf.intree_scc_varreplace_time_limitM*1000ULL*1000ULL
        *solver->conf.global_timeout_multiplier
        *0.5;
    time_limit = (double)time_limit * std::min(std::pow((double)(numCalls+1), 0.2), 3.0);

    aborted = false;
    uint64_t bogoprops = 0;
    uint32_t last_replace = std::numeric_limits<uint32_t>::max();
    uint32_t this_replace = solver->varReplacer->get_num_replaced_vars();
    while(last_replace != this_replace && !aborted) {
        last_replace = this_replace;
        solver->clauseCleaner->remove_and_clean_all();
        bool OK = solver->varReplacer->replace_if_enough_is_found(0, &bogoprops);
        if (!OK) {
            return false;
        }

        if (solver->varReplacer->get_scc_depth_warning_triggered()) {
            aborted = true;
            return solver->okay();
        }
        this_replace = solver->varReplacer->get_num_replaced_vars();

        if (bogoprops > time_limit) {
            aborted = true;
            return solver->okay();
        }
    }

    return true;
}

bool InTree::watches_only_contains_nonbin(const Lit lit) const
{
    watch_subarray_const ws = solver->watches[lit];
    for(const Watched w: ws) {
        if (w.isBin()) {
            return false;
        }
    }

    return true;
}

bool InTree::check_timeout_due_to_hyperbin()
{
    assert(!(solver->timedOutPropagateFull && solver->drat->enabled()));
    assert(!(solver->timedOutPropagateFull && solver->conf.simulate_drat));

    if (solver->timedOutPropagateFull
        && !solver->drat->enabled()
    ) {
        if (solver->conf.verbosity) {
            cout
            << "c [intree] intra-propagation timout,"
            << " turning off OTF hyper-bin&trans-red"
            << endl;
        }

        solver->conf.otfHyperbin = false;
        return true;
    }

    return false;
}

void InTree::fill_roots()
{
    //l is root if no clause of form (l, l2).

    roots.clear();
    for(uint32_t i = 0; i < solver->nVars()*2; i++)
    {
        Lit lit(i/2, i%2);
        if (solver->varData[lit.var()].removed != Removed::none
            || solver->value(lit) != l_Undef
        ) {
            continue;
        }

        if (watches_only_contains_nonbin(lit)) {
            roots.push_back(lit);
        }
    }
}

bool InTree::intree_probe()
{
    assert(solver->okay());
    queue.clear();
    reset_reason_stack.clear();
    solver->use_depth_trick = false;
    solver->perform_transitive_reduction = true;
    hyperbin_added = 0;
    removedIrredBin = 0;
    removedRedBin = 0;
    numCalls++;

    bool aborted = false;
    if (!replace_until_fixedpoint(aborted))
    {
        return solver->okay();
    }
    if (aborted) {
        if (solver->conf.verbosity) {
            cout
            << "c [intree] too expensive or depth exceeded during SCC: aborting"
            << endl;
        }
        solver->use_depth_trick = true;
        solver->perform_transitive_reduction = true;
        return true;
    }

    double myTime = cpuTime();
    bogoprops_to_use =
        solver->conf.intree_time_limitM*1000ULL*1000ULL
        *solver->conf.global_timeout_multiplier;
    bogoprops_to_use = (double)bogoprops_to_use * std::pow((double)(numCalls+1), 0.3);
    bogoprops_remain = bogoprops_to_use;

    fill_roots();
    randomize_roots();

    //Let's enqueue all ~root -s.
    for(Lit lit: roots) {
        enqueue(~lit, lit_Undef, false);
    }

    //clear seen
    for(QueueElem elem: queue) {
        if (elem.propagated != lit_Undef) {
            seen[elem.propagated.toInt()] = 0;
        }
    }
    const size_t orig_num_free_vars = solver->get_num_free_vars();

    tree_look();
    unmark_all_bins();

    const double time_used = cpuTime() - myTime;
    const double time_remain = float_div(bogoprops_remain, bogoprops_to_use);
    const bool time_out = (bogoprops_remain < 0);

    if (solver->conf.verbosity) {
        cout << "c [intree] Set "
        << (orig_num_free_vars - solver->get_num_free_vars())
        << " vars"
        << " hyper-added: " << hyperbin_added
        << " trans-irred::" << removedIrredBin
        << " trans-red::" << removedRedBin
        << solver->conf.print_times(time_used,  time_out, time_remain)
        << endl;
    }

    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "intree"
            , time_used
            , time_out
            , time_remain
        );
    }

    solver->use_depth_trick = true;
    solver->perform_transitive_reduction = true;
    return solver->okay();
}

void InTree::unmark_all_bins()
{
    for(watch_subarray wsub: solver->watches) {
        for(Watched& w: wsub) {
            if (w.isBin()) {
                w.unmark_bin_cl();
            }
        }
    }
}

void InTree::randomize_roots()
{
    for (size_t i = 0
        ; i + 1< roots.size()
        ; i++
    ) {
        std::swap(
            roots[i]
            , roots[i+solver->mtrand.randInt(roots.size()-1-i)]
        );
    }
}

void InTree::tree_look()
{
    assert(failed.empty());
    depth_failed.clear();
    depth_failed.push_back(false);
    solver->propStats.clear();

    bool timeout = false;
    while(!queue.empty())
    {
        if ((int64_t)solver->propStats.bogoProps
            + (int64_t)solver->propStats.otfHyperTime
            > bogoprops_remain
            || timeout
        ) {
            break;
        }

        const QueueElem elem = queue.front();
        queue.pop_front();

        if (solver->conf.verbosity >= 10) {
            cout << "Dequeued [[" << elem << "]] dec lev:"
            << solver->decisionLevel() << endl;
        }

        if (elem.propagated != lit_Undef) {
            timeout = handle_lit_popped_from_queue(elem.propagated, elem.other_lit, elem.red);
        } else {
            assert(solver->decisionLevel() > 0);
            solver->cancelUntil<false, true>(solver->decisionLevel()-1);

            depth_failed.pop_back();
            assert(!depth_failed.empty());

            if (reset_reason_stack.empty()) {
                assert(solver->decisionLevel() == 0);
            } else {
                assert(!reset_reason_stack.empty());
                ResetReason tmp = reset_reason_stack.back();
                reset_reason_stack.pop_back();
                if (tmp.var_reason_changed != var_Undef) {
                    solver->varData[tmp.var_reason_changed].reason = tmp.orig_propby;
                    if (solver->conf.verbosity >= 10) {
                        cout << "RESet reason for VAR " << tmp.var_reason_changed+1 << " to:  ????" << /*tmp.orig_propby.lit2() << */ " red: " << (int)tmp.orig_propby.isRedStep() << endl;
                    }
                }
            }
        }

        if (solver->decisionLevel() == 0) {
            if (!empty_failed_list()) {
                return;
            }
        }
    }

    bogoprops_remain -= (int64_t)solver->propStats.bogoProps + (int64_t)solver->propStats.otfHyperTime;

    solver->cancelUntil<false, true>(0);
    empty_failed_list();
}

bool InTree::handle_lit_popped_from_queue(const Lit lit, const Lit other_lit, const bool red)
{
    solver->new_decision_level();
    depth_failed.push_back(depth_failed.back());
    if (other_lit != lit_Undef) {
        reset_reason_stack.push_back(ResetReason(var_Undef, PropBy()));
    }

    bool timeout = false;

    if (solver->value(lit) == l_False
        || depth_failed.back() == 1
    ) {
        //l is failed.
        failed.push_back(~lit);
        if (solver->conf.verbosity >= 10) {
            cout << "Failed :" << ~lit << " level: " << solver->decisionLevel() << endl;
        }

        return false;
    }

    if (other_lit != lit_Undef) {
        //update 'other_lit' 's ancestor to 'lit'
        assert(solver->value(other_lit) == l_True);
        reset_reason_stack.back() = ResetReason(other_lit.var(), solver->varData[other_lit.var()].reason);
        solver->varData[other_lit.var()].reason = PropBy(~lit, red, false, false);
        if (solver->conf.verbosity >= 10) {
            cout << "Set reason for VAR " << other_lit.var()+1 << " to: " << ~lit << " red: " << (int)red << endl;
        }
    }

    if (solver->value(lit) == l_Undef) {
        solver->enqueue(lit);

        //Should do HHBR here
        bool ok;
        if (solver->conf.otfHyperbin) {
            uint64_t max_hyper_time = std::numeric_limits<uint64_t>::max();
            if (!solver->drat->enabled() &&
                !solver->conf.simulate_drat
            ) {
                max_hyper_time =
                solver->propStats.otfHyperTime
                + solver->propStats.bogoProps
                + 1600ULL*1000ULL*1000ULL;
            }

            Lit ret = solver->propagate_bfs(
                max_hyper_time //early-abort timeout
            );
            ok = (ret == lit_Undef);
            timeout = check_timeout_due_to_hyperbin();
        } else {
            ok = solver->propagate<true>().isNULL();
        }

        if (!ok && !timeout) {
            depth_failed.back() = 1;
            failed.push_back(~lit);
            if (solver->conf.verbosity >= 10) {
                cout << "(timeout?) Failed :" << ~lit << " level: " << solver->decisionLevel() << endl;
            }
        } else {
            hyperbin_added += solver->hyper_bin_res_all(false);
            std::pair<size_t, size_t> tmp = solver->remove_useless_bins(true);
            removedIrredBin += tmp.first;
            removedRedBin += tmp.second;
        }
        solver->uselessBin.clear();
        solver->needToAddBinClause.clear();
    }

    return timeout;
}

bool InTree::empty_failed_list()
{
    assert(solver->decisionLevel() == 0);
    for(const Lit lit: failed) {
        if (!solver->ok) {
            return false;
        }

        if (solver->value(lit) == l_Undef) {
            solver->enqueue(lit);
            *(solver->drat) << add << lit
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;
            solver->ok = solver->propagate<true>().isNULL();
            if (!solver->ok) {
                return false;
            }
        } else if (solver->value(lit) == l_False) {
            *(solver->drat) << add << ~lit
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;

            *(solver->drat) << add
            #ifdef STATS_NEEDED
            << solver->clauseID++
            << solver->sumConflicts
            #endif
            << fin;
            solver->ok = false;
            return false;
        }
    }
    failed.clear();

    return true;
}


// (lit V otherlit) exists -> (~otherlit, lit) in queue
// Next: (~otherLit, lit2) exists -> (~lit2, ~otherLit) in queue
// --> original ~otherlit got enqueued by lit2 = False (--> PropBy(lit2) ).

void InTree::enqueue(const Lit lit, const Lit other_lit, bool red_cl)
{
    queue.push_back(QueueElem(lit, other_lit, red_cl));
    assert(!seen[lit.toInt()]);
    seen[lit.toInt()] = 1;
    assert(solver->value(lit) == l_Undef);

    watch_subarray ws = solver->watches[lit];
    for(Watched& w: ws) {
        if (w.isBin()
            && seen[(~w.lit2()).toInt()] == 0
            && solver->value(w.lit2()) == l_Undef
        ) {
            //Mark both
            w.mark_bin_cl();
            Watched& other_w = findWatchedOfBin(solver->watches, w.lit2(), lit, w.red());
            other_w.mark_bin_cl();

            enqueue(~w.lit2(), lit, w.red());
        }
    }
    queue.push_back(QueueElem(lit_Undef, lit_Undef, false));
}


double InTree::mem_used() const
{
    double mem = 0;
    mem += sizeof(InTree);
    mem += roots.size()*sizeof(Lit);
    mem += failed.size()*sizeof(Lit);
    mem += reset_reason_stack.size()*sizeof(ResetReason);
    mem += queue.size()*sizeof(QueueElem);
    mem += depth_failed.size()*sizeof(char);
    return mem;
}

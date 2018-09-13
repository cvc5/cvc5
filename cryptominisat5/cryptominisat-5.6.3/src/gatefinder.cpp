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

#include "gatefinder.h"
#include "time_mem.h"
#include "solver.h"
#include "occsimplifier.h"
#include "subsumestrengthen.h"
#include "clauseallocator.h"
#include <array>
#include <utility>
#include "sqlstats.h"

using namespace CMSat;
using std::cout;
using std::endl;

GateFinder::GateFinder(OccSimplifier *_simplifier, Solver *_solver) :
    numDotPrinted(0)
    , simplifier(_simplifier)
    , solver(_solver)
    , seen(_solver->seen)
    , seen2(_solver->seen2)
    , toClear(solver->toClear)
{
    sizeSortedOcc.resize(solver->conf.maxGateBasedClReduceSize+1);
}

bool GateFinder::doAll()
{
    runStats.clear();
    orGates.clear();

    assert(solver->watches.get_smudged_list().empty());
    find_or_gates_and_update_stats();
    if (!all_simplifications_with_gates())
        goto end;

    if (solver->conf.doPrintGateDot) {
        print_graphviz_dot();
    }

end:
    solver->clean_occur_from_idx_types_only_smudged();
    if (solver->conf.verbosity) {
        if (solver->conf.verbosity >= 3) {
            runStats.print(solver->nVars());
        }
    }
    globalStats += runStats;

    orGates.clear();
    orGates.shrink_to_fit();
    solver->sumSearchStats.num_gates_found_last = orGates.size();

    return solver->okay();
}

void GateFinder::find_or_gates_and_update_stats()
{
    assert(solver->ok);

    double myTime = cpuTime();
    const int64_t orig_numMaxGateFinder =
        solver->conf.gatefinder_time_limitM*100LL*1000LL
        *solver->conf.global_timeout_multiplier;
    numMaxGateFinder = orig_numMaxGateFinder;
    simplifier->limit_to_decrease = &numMaxGateFinder;

    find_or_gates();

    for(const auto orgate: orGates) {
        if (orgate.red) {
            runStats.learntGatesSize += 2;
            runStats.numRed++;
        } else  {
            runStats.irredGatesSize += 2;
            runStats.numIrred++;
        }
    }
    const double time_used = cpuTime() - myTime;
    const bool time_out = (numMaxGateFinder <= 0);
    const double time_remain = float_div(numMaxGateFinder, orig_numMaxGateFinder);
    runStats.findGateTime = time_used;
    runStats.find_gate_timeout = time_out;
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "gate find"
            , time_used
            , time_out
            , time_remain
        );
    }

    if (solver->conf.verbosity) {
        cout << "c [occ-gates] found"
        << " irred:" << runStats.numIrred
        << " avg-s: " << std::fixed << std::setprecision(1)
        << float_div(runStats.irredGatesSize, runStats.numIrred)
        << " red: " << runStats.numRed
        /*<< " avg-s: " << std::fixed << std::setprecision(1)
        << float_div(learntGatesSize, numRed)*/
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }
}

bool GateFinder::shorten_with_all_or_gates()
{
    const double myTime = cpuTime();
    const int64_t orig_numMaxShortenWithGates =
        solver->conf.shorten_with_gates_time_limitM*1000LL*1000LL
        *solver->conf.global_timeout_multiplier;

    numMaxShortenWithGates = orig_numMaxShortenWithGates;
    simplifier->limit_to_decrease = &numMaxShortenWithGates;

    //Go through each gate, see if we can do something with it
    simplifier->cl_to_free_later.clear();
    for (const OrGate& gate: orGates) {
        if (numMaxShortenWithGates < 0
            || solver->must_interrupt_asap()
        ) {
            break;
        }

        if (!shortenWithOrGate(gate))
            break;
    }
    solver->clean_occur_from_removed_clauses();
    simplifier->free_clauses_to_free();

    const double time_used = cpuTime() - myTime;
    const bool time_out = (numMaxShortenWithGates <= 0);
    const double time_remain = float_div(numMaxShortenWithGates, orig_numMaxShortenWithGates);
    runStats.orBasedTime = time_used;
    runStats.or_based_timeout = time_out;
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "gate shorten cl"
            , time_used
            , time_out
            , time_remain
        );
    }

    if (solver->conf.verbosity) {
        cout << "c [occ-gates] shorten"
        << " cl: " << std::setw(5) << runStats.orGateUseful
        << " l-rem: " << std::setw(6) << runStats.litsRem
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }

    return solver->okay();
}

bool GateFinder::remove_clauses_with_all_or_gates()
{
    const int64_t orig_numMaxClRemWithGates =
        solver->conf.remove_cl_with_gates_time_limitM*1000LL*1000LL
        *solver->conf.global_timeout_multiplier;

    numMaxClRemWithGates = orig_numMaxClRemWithGates;
    simplifier->limit_to_decrease = &numMaxClRemWithGates;
    const double myTime = cpuTime();

    //Go through each gate, see if we can do something with it
    for (const OrGate& gate: orGates) {
        if (numMaxClRemWithGates < 0
            || solver->must_interrupt_asap()
        ) {
            break;
        }

        if (!remove_clauses_using_and_gate(gate, true, false))
            break;

        if (!remove_clauses_using_and_gate_tri(gate, true, false))
            break;
    }
    const double time_used = cpuTime() - myTime;
    const bool time_out = (numMaxClRemWithGates <= 0);
    const double time_remain = float_div(numMaxClRemWithGates, orig_numMaxClRemWithGates);
    runStats.andBasedTime = time_used;
    runStats.and_based_timeout = time_out;
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "gate rem cl"
            , time_used
            , time_out
            , time_remain
        );
    }

    if (solver->conf.verbosity) {
        cout << "c [occ-gates] rem"
        << " cl: " << runStats.andGateUseful
        << " avg s: " << std::setprecision(1)
        << float_div(runStats.clauseSizeRem, runStats.andGateUseful)
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }

    return solver->okay();
}

bool GateFinder::all_simplifications_with_gates()
{
    assert(solver->ok);

    //OR gate treatment
    if (solver->conf.doShortenWithOrGates) {
        if (!shorten_with_all_or_gates()) {
            return false;
        }
    }

    //AND gate treatment
    if (solver->conf.doRemClWithAndGates) {
        if (!remove_clauses_with_all_or_gates()) {
            return false;
        }
    }

    //EQ gate treatment
    if (solver->conf.doFindEqLitsWithGates) {
        const double myTime = cpuTime();
        runStats.varReplaced += findEqOrGates();

        const double time_used = cpuTime() - myTime;
        runStats.varReplaceTime += time_used;
        if (solver->sqlStats) {
            solver->sqlStats->time_passed_min(
                solver
                , "gate eq-var"
                , time_used
            );
        }

        if (solver->conf.verbosity) {
            cout << "c [occ-gates] eqlit"
            << " v-rep: " << std::setw(3) << runStats.varReplaced
            << solver->conf.print_times(time_used)
            << endl;
        }

        if (!solver->ok)
            return false;
    }

    return solver->okay();
}

size_t GateFinder::findEqOrGates()
{
    assert(solver->ok);
    size_t foundRep = 0;
    vector<OrGate> gates = orGates;
    std::sort(gates.begin(), gates.end(), GateCompareForEq());

    vector<Lit> tmp(2);
    for (uint32_t i = 1; i < gates.size(); i++) {
        const OrGate& gate1 = gates[i-1];
        const OrGate& gate2 = gates[i];

        if (gate1.lit1 == gate2.lit1
            && gate1.lit2 == gate2.lit2
            && gate1.rhs.var() != gate2.rhs.var()
       ) {
            foundRep++;
            tmp[0] = gate1.rhs.unsign();
            tmp[1] = gate2.rhs.unsign();
            const bool RHS = gate1.rhs.sign() ^ gate2.rhs.sign();
            if (!solver->add_xor_clause_inter(tmp, RHS, false))
                return foundRep;
        }
    }

    return foundRep;
}

void GateFinder::find_or_gates()
{
    if (solver->nVars() < 1)
        return;

    const size_t offs = solver->mtrand.randInt(solver->nVars()*2-1);
    for(size_t i = 0
        ; i < solver->nVars()*2
            && *simplifier->limit_to_decrease > 0
            && !solver->must_interrupt_asap()
        ; i++
    ) {
        const size_t at = (offs + i) % (solver->nVars()*2);
        const Lit lit = Lit::toLit(at);
        find_or_gates_in_sweep_mode(lit);
        find_or_gates_in_sweep_mode(~lit);
    }
}

void GateFinder::find_or_gates_in_sweep_mode(const Lit lit)
{
    assert(toClear.empty());
    watch_subarray_const ws = solver->watches[lit];
    *simplifier->limit_to_decrease -= ws.size();
    for(const Watched w: ws) {
        if (w.isBin() && !w.red()) {
            seen[(~w.lit2()).toInt()] = 1;
            toClear.push_back(~w.lit2());
        }
    }

    if (solver->conf.doCache && solver->conf.otfHyperbin) {
        const vector<LitExtra>& cache = solver->implCache[lit].lits;
        *simplifier->limit_to_decrease -= cache.size();
        for(const LitExtra l: cache) {
             if (l.getOnlyIrredBin()) {
                seen[(~l.getLit()).toInt()] = 1;
                toClear.push_back(~l.getLit());
            }
        }
    }

    watch_subarray_const ws2 = solver->watches[~lit];
    *simplifier->limit_to_decrease -= ws2.size();
    for(const Watched w: ws2) {
        if (w.isTri()
            && !w.red()
            && (seen[w.lit2().toInt()]
                || (solver->conf.doStamp && solver->conf.otfHyperbin && solver->find_with_stamp_a_or_b(~w.lit2(), lit)))
            && (seen[w.lit3().toInt()]
                || (solver->conf.doStamp && solver->conf.otfHyperbin && solver->find_with_stamp_a_or_b(~w.lit3(), lit)))
        ) {
            add_gate_if_not_already_inside(lit, w.lit2(), w.lit3());
        }
    }

    *simplifier->limit_to_decrease -= toClear.size();
    for(const Lit toclear: toClear) {
        seen[toclear.toInt()] = 0;
    }
    toClear.clear();
}


void GateFinder::add_gate_if_not_already_inside(
    const Lit rhs
    , const Lit lit1
    , const Lit lit2
) {
    OrGate gate(rhs, lit1, lit2, false);
    for (Watched ws: solver->watches[gate.rhs]) {
        if (ws.isIdx()
            && orGates[ws.get_idx()] == gate
        ) {
            return;
        }
    }
    link_in_gate(gate);
}

void GateFinder::link_in_gate(const OrGate& gate)
{
    const size_t at = orGates.size();
    orGates.push_back(gate);
    solver->watches[gate.rhs].push(Watched(at));
    solver->watches.smudge(gate.rhs);
}

bool GateFinder::shortenWithOrGate(const OrGate& gate)
{
    assert(solver->ok);

    //Find clauses that potentially could be shortened
    subs.clear();
    simplifier->sub_str->find_subsumed(
        std::numeric_limits< uint32_t >::max()
        , gate.getLits()
        , calcAbstraction(gate.getLits())
        , subs
    );

    for (size_t i = 0; i < subs.size(); i++) {
        ClOffset offset = subs[i];
        Clause& cl = *solver->cl_alloc.ptr(offset);

        //Don't shorten irred clauses with red gates
        // -- potential loss if e.g. red clause is removed later
        if ((!cl.red() && gate.red))
            continue;

        runStats.orGateUseful++;

        //Go through clause, check if RHS (rhs) is inside the clause
        //If it is, we have two possibilities:
        //1) a = b V c , clause: a V b V c V d
        //2) a = b V c , clause: -a V b V c V d
        //But we will simply ignore this. One of these clauses can be strengthened
        //the other subsumed. But let's ignore these, subsumption/strenghtening will take care of this
        bool rhsInside = false;
        for (Lit lit: cl) {
            if (gate.rhs.var() == lit.var()) {
                rhsInside = true;
                break;
            }
        }
        if (rhsInside)
            continue;

        if (solver->conf.verbosity >= 6) {
            cout << "OR gate-based cl-shortening" << endl;
            cout << "Gate used: " << gate << endl;
            cout << "orig Clause: " << cl<< endl;
        }

        //Set up future clause's lits
        vector<Lit> lits;
        for (const Lit lit: cl) {
            bool inGate = false;
            for (Lit lit2: gate.getLits()) {
                if (lit == lit2) {
                    inGate = true;
                    runStats.litsRem++;
                    break;
                }
            }

            if (!inGate)
                lits.push_back(lit);
        }
        if (!rhsInside) {
            lits.push_back(gate.rhs);
            runStats.litsRem--;
        }

        //Future clause's stat
        const bool red = cl.red();
        const ClauseStats stats = cl.stats;

        //Free the old clause and allocate new one
        (*solver->drat) << deldelay << cl << fin;
        simplifier->unlink_clause(offset, false, false, true);
        Clause* cl2 = solver->add_clause_int(lits, red, stats, false);
        (*solver->drat) << findelay;
        if (!solver->ok)
            return false;

        //If the clause is implicit, it's already linked in, ignore
        if (cl2 == NULL)
            continue;

        simplifier->linkInClause(*cl2);
        ClOffset offset2 = solver->cl_alloc.get_offset(cl2);
        simplifier->clauses.push_back(offset2);

        if (solver->conf.verbosity >= 6) {
            cout << "new clause after gate: " << lits << endl;
            cout << "-----------" << endl;
        }
    }

    return true;
}

void GateFinder::set_seen2_and_abstraction(
    const Clause& cl
    , cl_abst_type& abstraction
) {
    *simplifier->limit_to_decrease -= cl.size();
    for (const Lit lit: cl) {
        if (!seen2[lit.toInt()]) {
            seen2[lit.toInt()] = true;
            seen2Set.push_back(lit.toInt());
        }
        abstraction |= abst_var(lit.var());
    }
}

cl_abst_type GateFinder::calc_sorted_occ_and_set_seen2(
    const OrGate& gate
    , uint32_t& maxSize
    , uint32_t& minSize
    , const bool only_irred
) {
    assert(seen2Set.empty());
    cl_abst_type abstraction = 0;
    for (vector<ClOffset>& certain_size_occ: sizeSortedOcc)
        certain_size_occ.clear();

    watch_subarray_const csOther = solver->watches[~(gate.lit2)];
    *simplifier->limit_to_decrease -= csOther.size();
    for (const Watched ws: csOther) {
        if (!ws.isClause())
            continue;

        const ClOffset offset = ws.get_offset();
        const Clause& cl = *solver->cl_alloc.ptr(offset);
        if (cl.red() && only_irred)
            continue;

        //We might be contracting 2 irred clauses based on a learnt gate
        //would lead to UNSAT->SAT
        if (!cl.red() && gate.red)
            continue;

        //Clause too long, skip
        if (cl.size() > solver->conf.maxGateBasedClReduceSize)
            continue;

        maxSize = std::max(maxSize, cl.size());
        minSize = std::min(minSize, cl.size());
        sizeSortedOcc[cl.size()].push_back(offset);
        set_seen2_and_abstraction(cl, abstraction);
    }

    return abstraction;
}

void GateFinder::set_seen2_tri(
    const OrGate& gate
    , const bool only_irred
) {
    assert(seen2Set.empty());
    watch_subarray_const csOther = solver->watches[~(gate.lit2)];
    *simplifier->limit_to_decrease -= csOther.size();
    for (const Watched ws: csOther) {
        if (!ws.isTri())
            continue;

        if (ws.red() && only_irred)
            continue;

        //We might be contracting 2 irred clauses based on a learnt gate
        //would lead to UNSAT->SAT
        if (!ws.red() && gate.red)
            continue;

        const Lit lits[2] = {ws.lit2(), ws.lit3()};
        for (size_t i = 0; i < 2; i++) {
            const Lit lit = lits[i];
            if (!seen2[lit.toInt()]) {
                seen2[lit.toInt()] = 1;
                seen2Set.push_back(lit.toInt());
            }
        }
    }
}

cl_abst_type GateFinder::calc_abst_and_set_seen(
    const Clause& cl
    , const OrGate& gate
) {
    cl_abst_type abst = 0;
    for (const Lit lit: cl) {
        //lit1 doesn't count into abstraction
        if (lit == ~(gate.lit1))
            continue;

        seen[lit.toInt()] = 1;
        abst |= abst_var(lit.var());
    }
    abst |= abst_var((~(gate.lit2)).var());

    return abst;
}

bool GateFinder::check_seen_and_gate_against_cl(
    const Clause& this_cl
    , const OrGate& gate
) {
    *(simplifier->limit_to_decrease) -= this_cl.size();
    for (const Lit lit: this_cl) {

        //We know this is inside, skip
        if (lit == ~(gate.lit1))
            continue;

        //If some weird variable is inside, skip
        if (   lit.var() == gate.lit2.var()
            || lit.var() == gate.rhs.var()
            //A lit is inside this clause isn't inside the others
            || !seen2[lit.toInt()]
        ) {
            return false;
        }
    }
    return true;
}

bool GateFinder::check_seen_and_gate_against_lit(
    const Lit lit
    , const OrGate& gate
) {
    //If some weird variable is inside, skip
    if (   lit.var() == gate.lit2.var()
        || lit.var() == gate.rhs.var()
        //A lit is inside this clause isn't inside the others
        || !seen2[lit.toInt()]
    ) {
        return false;
    }

    return true;
}

ClOffset GateFinder::find_pair_for_and_gate_reduction(
    const Watched& ws
    , const size_t minSize
    , const size_t maxSize
    , const cl_abst_type general_abst
    , const OrGate& gate
    , const bool only_irred
) {
    //Only long clauses
    if (!ws.isClause())
        return CL_OFFSET_MAX;

    const ClOffset this_cl_offs = ws.get_offset();
    Clause& this_cl = *solver->cl_alloc.ptr(this_cl_offs);
    if ((ws.getAbst() | general_abst) != general_abst
        || (this_cl.red() && only_irred)
        || (!this_cl.red() && gate.red)
        || this_cl.size() > solver->conf.maxGateBasedClReduceSize
        || this_cl.size() > maxSize //Size must be smaller or equal to maxSize
        || this_cl.size() < minSize //Size must be larger or equal than minsize
        || sizeSortedOcc[this_cl.size()].empty()) //this bracket for sizeSortedOcc must be non-empty
    {
        //cout << "Not even possible, this clause cannot match any other" << endl;
        return CL_OFFSET_MAX;
    }

    if (!check_seen_and_gate_against_cl(this_cl, gate))
        return CL_OFFSET_MAX;


    const cl_abst_type this_cl_abst = calc_abst_and_set_seen(this_cl, gate);
    const ClOffset other_cl_offs = findAndGateOtherCl(
        sizeSortedOcc[this_cl.size()] //in this occur list that contains clauses of specific size
        , ~(gate.lit2) //this is the LIT that is meant to be in the clause
        , this_cl_abst //clause MUST match this abst
        , gate.red
        , only_irred
    );

    //Clear 'seen' from bits set
    *(simplifier->limit_to_decrease) -= this_cl.size();
    for (const Lit lit: this_cl) {
        seen[lit.toInt()] = 0;
    }

    return other_cl_offs;
}

bool GateFinder::find_pair_for_and_gate_reduction_tri(
    const Watched& ws
    , const OrGate& gate
    , const bool only_irred
    , Watched& found_pair
) {
    //Only long clauses
    if (!ws.isTri())
        return false;

    if (ws.red() && only_irred) {
        //cout << "Not even possible, this clause cannot match any other" << endl;
        return false;
    }

    //Check that we are not removing irred info based on learnt gate
    if (!ws.red() && gate.red)
        return false;

    if (!check_seen_and_gate_against_lit(ws.lit2(), gate)
        || !check_seen_and_gate_against_lit(ws.lit3(), gate))
    {
        return false;
    }

    seen[ws.lit2().toInt()] = 1;
    seen[ws.lit3().toInt()] = 1;
    const bool ret = findAndGateOtherCl_tri(
        solver->watches[~(gate.lit2)]
        , gate.red
        , only_irred
        , found_pair
    );

    seen[ws.lit2().toInt()] = 0;
    seen[ws.lit3().toInt()] = 0;

    return ret;
}

bool GateFinder::remove_clauses_using_and_gate(
    const OrGate& gate
    , const bool really_remove
    , const bool only_irred
) {
    assert(clToUnlink.empty());
    if (solver->watches[~(gate.lit1)].empty()
        || solver->watches[~(gate.lit2)].empty()
    ) {
        return solver->okay();
    }

    uint32_t maxSize = 0;
    uint32_t minSize = std::numeric_limits<uint32_t>::max();
    cl_abst_type general_abst = calc_sorted_occ_and_set_seen2(gate, maxSize, minSize, only_irred);
    general_abst |= abst_var(gate.lit1.var());
    if (maxSize == 0)
        return solver->okay();

    watch_subarray cs = solver->watches[~(gate.lit1)];
    *simplifier->limit_to_decrease -= cs.size();
    for (const Watched ws: cs) {
        if (*simplifier->limit_to_decrease < 0)
            break;

        const ClOffset other_cl_offs = find_pair_for_and_gate_reduction(
            ws, minSize, maxSize, general_abst, gate, only_irred
        );

        if (really_remove
           && other_cl_offs != CL_OFFSET_MAX
        ) {
            const ClOffset this_cl_offs = ws.get_offset();
            assert(other_cl_offs != this_cl_offs);
            clToUnlink.insert(other_cl_offs);
            clToUnlink.insert(this_cl_offs);
            treatAndGateClause(other_cl_offs, gate, this_cl_offs);
        }

        if (!solver->ok)
            return false;
    }

    //Clear from seen2 bits that have been set
    *(simplifier->limit_to_decrease) -= seen2Set.size();
    for(const size_t at: seen2Set) {
        seen2[at] = 0;
    }
    seen2Set.clear();

    //Now that all is computed, remove those that need removal
    for(const ClOffset offset: clToUnlink) {
        simplifier->unlink_clause(offset);
    }
    clToUnlink.clear();

    return solver->okay();
}

bool GateFinder::remove_clauses_using_and_gate_tri(
    const OrGate& gate
    , const bool really_remove
    , const bool only_irred
) {
    if (solver->watches[~(gate.lit1)].empty()
        || solver->watches[~(gate.lit2)].empty()
    ) {
        return solver->okay();
    }
    tri_to_unlink.clear();

    set_seen2_tri(gate, only_irred);
    watch_subarray_const cs = solver->watches[~(gate.lit1)];
    *simplifier->limit_to_decrease -= cs.size();
    for (const Watched ws: cs) {
        if (*simplifier->limit_to_decrease < 0)
            break;

        Watched other_ws;
        const bool found_pair = find_pair_for_and_gate_reduction_tri(
            ws, gate, only_irred, other_ws
        );

        if (really_remove && found_pair) {
            runStats.andGateUseful++;
            runStats.clauseSizeRem += 3;

            tri_to_unlink.insert(TriToUnlink(ws.lit2(), ws.lit3(), ws.red()));
            solver->detach_tri_clause(~(gate.lit2), other_ws.lit2(), other_ws.lit3(), other_ws.red());
            vector<Lit> lits = {~(gate.rhs), ws.lit2(), ws.lit3()};
            solver->add_clause_int(
                lits
                , ws.red() && other_ws.red()
                , ClauseStats()
                , false //don't attach/propagate
            );
            if (!solver->ok)
                return false;
        }
    }

    //Clear from seen2 bits that have been set
    *(simplifier->limit_to_decrease) -= seen2Set.size();
    for(const size_t at: seen2Set) {
        seen2[at] = false;
    }
    seen2Set.clear();

    for(const TriToUnlink tri: tri_to_unlink) {
        solver->detach_tri_clause(~(gate.lit1), tri.lit2, tri.lit3, tri.red);
    }
    tri_to_unlink.clear();

    return solver->okay();
}

void GateFinder::treatAndGateClause(
    const ClOffset other_cl_offset
    , const OrGate& gate
    , const ClOffset this_cl_offset
) {
    //Update stats
    runStats.andGateUseful++;
    const Clause& this_cl = *solver->cl_alloc.ptr(this_cl_offset);
    runStats.clauseSizeRem += this_cl.size();

    if (solver->conf.verbosity >= 6) {
        cout << "AND gate-based cl rem" << endl;
        cout << "clause 1: " << this_cl << endl;
        //cout << "clause 2: " << *clauses[other_cl_offset.index] << endl;
        cout << "gate : " << gate << endl;
    }

    //Put into 'lits' the literals of the clause
    vector<Lit> lits;
    *simplifier->limit_to_decrease -= this_cl.size()*2;
    for (const Lit lit: this_cl) {
        if (lit != ~(gate.lit1)) {
            lits.push_back(lit);
            assert(lit.var() != gate.rhs.var());
            assert(lit.var() != gate.lit1.var());
            assert(lit.var() != gate.lit2.var());
        }
    }
    lits.push_back(~(gate.rhs));

    //Calculate learnt & glue
    const Clause& other_cl = *solver->cl_alloc.ptr(other_cl_offset);
    const bool red = other_cl.red() && this_cl.red();
    ClauseStats stats = ClauseStats::combineStats(this_cl.stats, other_cl.stats);

    if (solver->conf.verbosity >= 6) {
        cout << "gate new clause:" << lits << endl;
        cout << "-----------" << endl;
    }

    //Create clause (but don't attach)
    Clause* clNew = solver->add_clause_int(lits, red, stats, false);

    //Link in clause properly (not regular attach)
    if (clNew != NULL) {
        simplifier->linkInClause(*clNew);
        ClOffset offsetNew = solver->cl_alloc.get_offset(clNew);
        simplifier->clauses.push_back(offsetNew);
    }
}

ClOffset GateFinder::findAndGateOtherCl(
    const vector<ClOffset>& this_sizeSortedOcc
    , const Lit otherLit
    , const cl_abst_type abst
    , const bool gate_is_red
    , const bool only_irred
) {
    *(simplifier->limit_to_decrease) -= this_sizeSortedOcc.size();
    for (const ClOffset offset: this_sizeSortedOcc) {
        const Clause& cl = *solver->cl_alloc.ptr(offset);
        if (cl.red() && only_irred)
            continue;

        if (!cl.red() && gate_is_red)
            continue;

        //abstraction must match
        if (cl.abst != abst)
            continue;

        *(simplifier->limit_to_decrease) -= cl.size()/2+5;
        for (const Lit lit: cl) {
            //we skip the other lit in the gate
            if (lit == otherLit)
                continue;

            //Seen is perfectly correct, everything must match
            if (!seen[lit.toInt()])
                goto next;

        }
        return offset;
        next:;
    }

    return CL_OFFSET_MAX;
}

bool GateFinder::findAndGateOtherCl_tri(
    watch_subarray_const ws_list
    , const bool gate_is_red
    , const bool only_irred
    , Watched& ret
) {
    *(simplifier->limit_to_decrease) -= ws_list.size();
    for (const Watched& ws: ws_list) {
        if (!ws.isTri())
            continue;

        if (ws.red() && only_irred)
            continue;

        if (!ws.red() && gate_is_red)
            continue;

        if (seen[ws.lit2().toInt()]
            && seen[ws.lit3().toInt()]
        ) {
            ret = ws;
            return true;
        }
    }

    return false;
}

void GateFinder::print_graphviz_dot2()
{
    std::stringstream ss;
    ss << "Gates" << (numDotPrinted++) << ".dot";
    std::string filenename = ss.str();
    std::ofstream file(filenename.c_str(), std::ios::out);
    file << "digraph G {" << endl;
    vector<bool> gateUsed;
    gateUsed.resize(orGates.size(), false);
    size_t index = 0;
    for (const OrGate orGate: orGates) {
        index++;
        for (const Lit lit: orGate.getLits()) {
            for (Watched ws: solver->watches[lit]) {
                if (!ws.isIdx()) {
                    continue;
                }
                uint32_t at = ws.get_idx();

                //The same one, skip
                if (at == index)
                    continue;

                file << "Gate" << at;
                gateUsed[at] = true;
                file << " -> ";

                file << "Gate" << index;
                gateUsed[index] = true;

                file << "[arrowsize=\"0.4\"];" << endl;
            }

            /*vector<uint32_t>& occ2 = gateOccEq[(~*it2).toInt()];
            for (vector<uint32_t>::const_iterator it3 = occ2.begin(), end3 = occ2.end(); it3 != end3; it3++) {
                if (*it3 == index) continue;

                file << "Gate" << *it3;
                gateUsed[*it3] = true;
                file << " -> ";

                file << "Gate" << index;
                gateUsed[index] = true;

                file << "[style = \"dotted\", arrowsize=\"0.4\"];" << endl;
            }*/
        }
    }

    index = 0;
    for (const OrGate orGate: orGates) {
        index++;

        if (gateUsed[index]) {
            file << "Gate" << index << " [ shape=\"point\"";
            file << ", size = 0.8";
            file << ", style=\"filled\"";
            if (orGate.red)
                file << ", color=\"darkseagreen4\"";
            else
                file << ", color=\"darkseagreen\"";

            file << "];" << endl;
        }
    }

    file  << "}" << endl;
    file.close();
    cout << "c Printed gate structure to file " << filenename << endl;
}

void GateFinder::print_graphviz_dot()
{
    print_graphviz_dot2();
}

GateFinder::Stats& GateFinder::Stats::operator+=(const Stats& other)
{
    findGateTime += other.findGateTime;
    find_gate_timeout += other.find_gate_timeout;
    orBasedTime += other.orBasedTime;
    or_based_timeout += other.or_based_timeout;
    varReplaceTime += other.varReplaceTime;
    andBasedTime += other.andBasedTime;
    and_based_timeout += other.and_based_timeout;
    erTime += other.erTime;

    //OR-gate
    orGateUseful += other.orGateUseful;
    numLongCls += other.numLongCls;
    numLongClsLits += other.numLongClsLits;
    litsRem += other.litsRem;
    varReplaced += other.varReplaced;

    //And-gate
    andGateUseful += other.andGateUseful;
    clauseSizeRem += other.clauseSizeRem;

    //ER
    numERVars += other.numERVars;

    //Gates
    learntGatesSize += other.learntGatesSize;
    numRed += other.numRed;
    irredGatesSize += other.irredGatesSize;
    numIrred += other.numIrred;

    return *this;
}

void GateFinder::Stats::print(const size_t nVars) const
{
    cout << "c -------- GATE FINDING ----------" << endl;
    print_stats_line("c time"
        , total_time()
    );

    print_stats_line("c find gate time"
        , findGateTime
        , stats_line_percent(findGateTime, total_time())
        , "% time"
    );

    print_stats_line("c gate-based cl-sh time"
        , orBasedTime
        , stats_line_percent(orBasedTime, total_time())
        , "% time"
    );

    print_stats_line("c gate-based cl-rem time"
        , andBasedTime
        , stats_line_percent(andBasedTime, total_time())
        , "% time"
    );

    print_stats_line("c gate-based varrep time"
        , varReplaceTime
        , stats_line_percent(varReplaceTime, total_time())
        , "% time"
    );

    print_stats_line("c gatefinder cl-short"
        , orGateUseful
        , stats_line_percent(orGateUseful, numLongCls)
        , "% long cls"
    );

    print_stats_line("c gatefinder lits-rem"
        , litsRem
        , stats_line_percent(litsRem, numLongClsLits)
        , "% long cls lits"
    );

    print_stats_line("c gatefinder cl-rem"
        , andGateUseful
        , stats_line_percent(andGateUseful, numLongCls)
        , "% long cls"
    );

    print_stats_line("c gatefinder cl-rem's lits"
        , clauseSizeRem
        , stats_line_percent(clauseSizeRem, numLongClsLits)
        , "% long cls lits"
    );

    print_stats_line("c gatefinder var-rep"
        , varReplaced
        , stats_line_percent(varReplaced, nVars)
        , "% vars"
    );

    cout << "c -------- GATE FINDING END ----------" << endl;
}


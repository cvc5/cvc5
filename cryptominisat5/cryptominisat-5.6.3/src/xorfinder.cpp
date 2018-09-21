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

#include "xorfinder.h"
#include "time_mem.h"
#include "solver.h"
#include "occsimplifier.h"
#include "clauseallocator.h"
#include "sqlstats.h"

#include <limits>
//#define XOR_DEBUG

using namespace CMSat;
using std::cout;
using std::endl;

XorFinder::XorFinder(OccSimplifier* _occsimplifier, Solver* _solver) :
    occsimplifier(_occsimplifier)
    , solver(_solver)
    , toClear(_solver->toClear)
{
}

void XorFinder::find_xors_based_on_long_clauses()
{
    #ifdef DEBUG_MARKED_CLAUSE
    assert(solver->no_marked_clauses());
    #endif

    vector<Lit> lits;
    for (vector<ClOffset>::iterator
        it = occsimplifier->clauses.begin()
        , end = occsimplifier->clauses.end()
        ; it != end && xor_find_time_limit > 0
        ; ++it
    ) {
        ClOffset offset = *it;
        Clause* cl = solver->cl_alloc.ptr(offset);
        xor_find_time_limit -= 1;

        //Already freed
        if (cl->freed() || cl->getRemoved()) {
            continue;
        }

        //Too large -> too expensive
        if (cl->size() > solver->conf.maxXorToFind) {
            continue;
        }

        //If not tried already, find an XOR with it
        if (!cl->stats.marked_clause ) {
            cl->stats.marked_clause = true;
            assert(!cl->getRemoved());

            size_t needed_per_ws = 1ULL << (cl->size()-2);
            //let's allow shortened clauses
            needed_per_ws >>= 1;

            for(const Lit lit: *cl) {
                if (solver->watches[lit].size() < needed_per_ws) {
                    goto next;
                }
                if (solver->watches[~lit].size() < needed_per_ws) {
                    goto next;
                }
            }

            lits.resize(cl->size());
            std::copy(cl->begin(), cl->end(), lits.begin());
            findXor(lits, offset, cl->abst);
            next:;
        }
    }
}

void XorFinder::clean_equivalent_xors(vector<Xor>& txors)
{
    if (!txors.empty()) {
        for(Xor& x: txors) {
            std::sort(x.begin(), x.end());
        }
        std::sort(txors.begin(), txors.end());

        vector<Xor>::iterator i = txors.begin();
        vector<Xor>::iterator j = i;
        i++;
        uint64_t size = 1;
        for(vector<Xor>::iterator end = txors.end(); i != end; i++) {
            if (*j != *i) {
                j++;
                *j = *i;
                size++;
            }
        }
        txors.resize(size);
    }
}

void XorFinder::find_xors()
{
    runStats.clear();
    runStats.numCalls = 1;
    grab_mem();
    if ((solver->conf.xor_var_per_cut + 2) > solver->conf.maxXorToFind) {
        if (solver->conf.verbosity) {
            cout << "c WARNING updating max XOR to find to "
            << (solver->conf.xor_var_per_cut + 2)
            << " as the current number was lower than the cutting number" << endl;
        }
        solver->conf.maxXorToFind = solver->conf.xor_var_per_cut + 2;
    }

    xors.clear();
    double myTime = cpuTime();
    const int64_t orig_xor_find_time_limit =
        1000LL*1000LL*solver->conf.xor_finder_time_limitM
        *solver->conf.global_timeout_multiplier;

    xor_find_time_limit = orig_xor_find_time_limit;

    occsimplifier->sort_occurs_and_set_abst();
    if (solver->conf.verbosity) {
        cout << "c [occ-xor] sort occur list T: " << (cpuTime()-myTime) << endl;
    }

    #ifdef DEBUG_MARKED_CLAUSE
    assert(solver->no_marked_clauses());
    #endif

    find_xors_based_on_long_clauses();
    assert(runStats.foundXors == xors.size());

    //clean them of equivalent XORs
    clean_equivalent_xors(xors);

    //Cleanup
    for(ClOffset offset: occsimplifier->clauses) {
        Clause* cl = solver->cl_alloc.ptr(offset);
        cl->stats.marked_clause = false;
    }

    //Print stats
    const bool time_out = (xor_find_time_limit < 0);
    const double time_remain = float_div(xor_find_time_limit, orig_xor_find_time_limit);
    runStats.findTime = cpuTime() - myTime;
    runStats.time_outs += time_out;
    solver->sumSearchStats.num_xors_found_last = xors.size();
    print_found_xors();

    if (solver->conf.verbosity) {
        runStats.print_short(solver, time_remain);
    }
    globalStats += runStats;

    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "xor-find"
            , cpuTime() - myTime
            , time_out
            , time_remain
        );
    }
}

void XorFinder::print_found_xors()
{
    if (solver->conf.verbosity >= 5) {
        cout << "c Found XORs: " << endl;
        for(vector<Xor>::const_iterator
            it = xors.begin(), end = xors.end()
            ; it != end
            ; ++it
        ) {
            cout << "c " << *it << endl;
        }
    }
}

void XorFinder::add_xors_to_solver()
{
    solver->xorclauses = xors;
    #if defined(SLOW_DEBUG) || defined(XOR_DEBUG)
    for(const Xor& x: xors) {
        for(uint32_t v: x) {
            assert(solver->varData[v].removed == Removed::none);
        }
    }
    #endif
}

void XorFinder::findXor(vector<Lit>& lits, const ClOffset offset, cl_abst_type abst)
{
    //Set this clause as the base for the XOR, fill 'seen'
    xor_find_time_limit -= lits.size()/4+1;
    poss_xor.setup(lits, offset, abst, occcnt);

    //Run findXorMatch for the 2 smallest watchlists
    Lit slit = lit_Undef;
    Lit slit2 = lit_Undef;
    uint32_t smallest = std::numeric_limits<uint32_t>::max();
    uint32_t smallest2 = std::numeric_limits<uint32_t>::max();
    for (size_t i = 0, end = lits.size(); i < end; i++) {
        const Lit lit = lits[i];
        uint32_t num = solver->watches[lit].size();
        num += solver->watches[~lit].size();
        if (num < smallest) {
            slit2 = slit;
            smallest2 = smallest;

            slit = lit;
            smallest = num;
        } else if (num < smallest2) {
            slit2 = lit;
            smallest2 = num;
        }
    }
    findXorMatch(solver->watches[slit], slit);
    findXorMatch(solver->watches[~slit], ~slit);
    findXorMatch(solver->watches[slit2], slit2);
    findXorMatch(solver->watches[~slit2], ~slit2);

    if (poss_xor.foundAll()) {
        std::sort(lits.begin(), lits.end());
        Xor found_xor(lits, poss_xor.getRHS());
        #if defined(SLOW_DEBUG) || defined(XOR_DEBUG)
        for(Lit lit: lits) {
            assert(solver->varData[lit.var()].removed == Removed::none);
        }
        #endif

        add_found_xor(found_xor);
        for(ClOffset offs: poss_xor.get_offsets()) {
            Clause* cl = solver->cl_alloc.ptr(offs);
            assert(!cl->getRemoved());
            cl->set_used_in_xor(true);
        }
    }
    poss_xor.clear_seen(occcnt);
}

void XorFinder::add_found_xor(const Xor& found_xor)
{
    xors.push_back(found_xor);
    runStats.foundXors++;
    runStats.sumSizeXors += found_xor.size();
}

void XorFinder::findXorMatch(watch_subarray_const occ, const Lit wlit)
{
    xor_find_time_limit -= (int64_t)occ.size()/8+1;
    for (const Watched& w: occ) {
        if (w.isIdx()) {
            continue;
        }
        assert(poss_xor.getSize() > 2);

        if (w.isBin()) {
            #ifdef SLOW_DEBUG
            assert(occcnt[wlit.var()]);
            #endif
            if (!occcnt[w.lit2().var()]) {
                goto end;
            }

            binvec.clear();
            binvec.resize(2);
            binvec[0] = w.lit2();
            binvec[1] = wlit;
            if (binvec[0] > binvec[1]) {
                std::swap(binvec[0], binvec[1]);
            }

            xor_find_time_limit -= 1;
            poss_xor.add(binvec, std::numeric_limits<ClOffset>::max(), varsMissing);
            if (poss_xor.foundAll())
                break;
        } else {
            if (w.getBlockedLit().toInt() == lit_Undef.toInt())
                //Clauses are ordered, lit_Undef means it's larger than maxXorToFind
                break;

            if (w.getBlockedLit().toInt() == lit_Error.toInt())
                //lit_Error means it's freed or removed, and it's ordered so no more
                break;

            if ((w.getBlockedLit().toInt() | poss_xor.getAbst()) != poss_xor.getAbst())
                continue;

            xor_find_time_limit -= 3;
            const ClOffset offset = w.get_offset();
            Clause& cl = *solver->cl_alloc.ptr(offset);
            if (cl.freed() || cl.getRemoved()) {
                //Clauses are ordered!!
                break;
            }

            //Allow the clause to be smaller or equal in size
            if (cl.size() > poss_xor.getSize()) {
                //clauses are ordered!!
                break;
            }

            //Doesn't contain variables not in the original clause
            #if defined(SLOW_DEBUG) || defined(XOR_DEBUG)
            assert(cl.abst == calcAbstraction(cl));
            #endif
            if ((cl.abst | poss_xor.getAbst()) != poss_xor.getAbst())
                continue;

            //Check RHS, vars inside
            bool rhs = true;
            for (const Lit cl_lit :cl) {
                //early-abort, contains literals not in original clause
                if (!occcnt[cl_lit.var()])
                    goto end;

                rhs ^= cl_lit.sign();
            }
            //either the invertedness has to match, or the size must be smaller
            if (rhs != poss_xor.getRHS() && cl.size() == poss_xor.getSize())
                continue;

            //If the size of this clause is the same of the base clause, then
            //there is no point in using this clause as a base for another XOR
            //because exactly the same things will be found.
            if (cl.size() == poss_xor.getSize()) {
                cl.stats.marked_clause = true;;
            }

            xor_find_time_limit -= cl.size()/4+1;
            poss_xor.add(cl, offset, varsMissing);
            if (poss_xor.foundAll())
                break;
        }
        end:;
    }

    if (solver->conf.doCache &&
        solver->conf.useCacheWhenFindingXors &&
        !poss_xor.foundAll()
    ) {
        const TransCache& cache1 = solver->implCache[wlit];
        for (const LitExtra litExtra: cache1.lits) {
            const Lit otherlit = litExtra.getLit();
            if (!occcnt[otherlit.var()]) {
                continue;
            }

            binvec.clear();
            binvec.resize(2);
            binvec[0] = otherlit;
            binvec[1] = wlit;
            if (binvec[0] > binvec[1]) {
                std::swap(binvec[0], binvec[1]);
            }

            xor_find_time_limit -= 1;
            poss_xor.add(binvec, std::numeric_limits<ClOffset>::max(), varsMissing);
            if (poss_xor.foundAll())
                break;
        }
    }
}

vector<Xor> XorFinder::remove_xors_without_connecting_vars(const vector<Xor>& this_xors)
{
    if (this_xors.empty())
        return this_xors;

    double myTime = cpuTime();
    vector<Xor> ret;
    assert(toClear.empty());

    //Fill seen with vars used
    uint32_t non_empty = 0;
    for(const Xor& x: this_xors) {
        if (x.size() != 0) {
            non_empty++;
        }

        for(uint32_t v: x) {
            if (solver->seen[v] == 0) {
                toClear.push_back(Lit(v, false));
            }

            if (solver->seen[v] < 2) {
                solver->seen[v]++;
            }
        }
    }

    vector<Xor>::const_iterator i = this_xors.begin();
    for(vector<Xor>::const_iterator end = this_xors.end()
        ; i != end
        ; i++
    ) {
        if (xor_has_interesting_var(*i)) {
            ret.push_back(*i);
        }
    }

    for(Lit l: toClear) {
        solver->seen[l.var()] = 0;
    }
    toClear.clear();

    double time_used = cpuTime() - myTime;
    if (solver->conf.verbosity) {
        cout << "c [xor-rem-unconnected] left with " <<  ret.size()
        << " xors from " << non_empty << " non-empty xors"
        << solver->conf.print_times(time_used)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "xor-rem-no-connecting-vars"
            , time_used
        );
    }

    return ret;
}

bool XorFinder::xor_together_xors(vector<Xor>& this_xors)
{
    if (occcnt.size() != solver->nVars())
        grab_mem();

    if (this_xors.empty())
        return solver->okay();

    #ifdef SLOW_DEBUG
    for(auto x: occcnt) {
        assert(x == 0);
    }
    #endif

    assert(solver->okay());
    assert(solver->decisionLevel() == 0);
    assert(solver->watches.get_smudged_list().empty());
    const size_t origsize = this_xors.size();

    uint32_t xored = 0;
    const double myTime = cpuTime();
    assert(toClear.empty());

    //Link in xors into watchlist
    for(size_t i = 0; i < this_xors.size(); i++) {
        const Xor& x = this_xors[i];
        for(uint32_t v: x) {
            if (occcnt[v] == 0) {
                toClear.push_back(Lit(v, false));
            }
            occcnt[v]++;

            Lit l(v, false);
            assert(solver->watches.size() > l.toInt());
            solver->watches[l].push(Watched(i)); //Idx watch
            solver->watches.smudge(l);
        }
    }

    //until fixedpoint
    bool changed = true;
    while(changed) {
        changed = false;
        interesting.clear();
        for(const Lit l: toClear) {
            if (occcnt[l.var()] == 2) {
                interesting.push_back(l.var());
            }
        }

        while(!interesting.empty()) {
            #ifdef SLOW_DEBUG
            {
                vector<uint32_t> check;
                check.resize(solver->nVars(), 0);
                for(size_t i = 0; i < this_xors.size(); i++) {
                    const Xor& x = this_xors[i];
                    for(uint32_t v: x) {
                        check[v]++;
                    }
                }
                for(size_t i = 0; i < solver->nVars(); i++) {
                    assert(check[i] == occcnt[i]);
                }
            }
            #endif

            const uint32_t v = interesting.back();
            interesting.resize(interesting.size()-1);
            if (occcnt[v] != 2)
                continue;

            size_t idxes[2];
            unsigned at = 0;
            size_t i2 = 0;
            assert(solver->watches.size() > Lit(v, false).toInt());
            watch_subarray ws = solver->watches[Lit(v, false)];

            for(size_t i = 0; i < ws.size(); i++) {
                const Watched& w = ws[i];
                if (!w.isIdx()) {
                    ws[i2++] = ws[i];
                } else if (this_xors[w.get_idx()] != Xor()) {
                    assert(at < 2);
                    idxes[at] = w.get_idx();
                    at++;
                }
            }
            assert(at == 2);
            ws.resize(i2);

            if (this_xors[idxes[0]] == this_xors[idxes[1]]) {
                //Equivalent, so delete one
                this_xors[idxes[0]] = Xor();

                //Re-attach the other, remove the occur of the one we deleted
                const Xor& x = this_xors[idxes[1]];
                solver->watches[Lit(v, false)].push(Watched(idxes[1]));
                for(uint32_t v2: x) {
                    Lit l(v2, false);
                    assert(occcnt[l.var()] >= 2);
                    occcnt[l.var()]--;
                    if (occcnt[l.var()] == 2) {
                        interesting.push_back(l.var());
                    }
                }
            } else {
                uint32_t clash_num;
                vector<uint32_t> vars = xor_two(this_xors[idxes[0]], this_xors[idxes[1]], clash_num);
                if (clash_num > 1) {
                    //add back to ws
                    ws.push(Watched(idxes[0]));
                    ws.push(Watched(idxes[1]));
                    continue;
                }
                occcnt[v] -= 2;
                assert(occcnt[v] == 0);

                Xor x_new(vars, this_xors[idxes[0]].rhs ^ this_xors[idxes[1]].rhs);
                changed = true;
                this_xors.push_back(x_new);
                for(uint32_t v2: x_new) {
                    Lit l(v2, false);
                    solver->watches[l].push(Watched(this_xors.size()-1));
                    assert(occcnt[l.var()] >= 1);
                    if (occcnt[l.var()] == 2) {
                        interesting.push_back(l.var());
                    }
                }
                this_xors[idxes[0]] = Xor();
                this_xors[idxes[1]] = Xor();
                xored++;
            }
        }
    }

    for(const Lit l: toClear) {
        occcnt[l.var()] = 0;
    }
    toClear.clear();

    solver->clean_occur_from_idx_types_only_smudged();
    clean_xors_from_empty();
    double recur_time = cpuTime() - myTime;
        if (solver->conf.verbosity) {
        cout
        << "c [xor-together] xored together " << xored << " xors"
        << " orig num xors: " << origsize
        << solver->conf.print_times(recur_time)
        << endl;
    }


    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "xor-xor-together"
            , recur_time
        );
    }

    #if defined(SLOW_DEBUG) || defined(XOR_DEBUG)
    //Make sure none is 2.
    assert(toClear.empty());
    for(const Xor& x: this_xors) {
        for(uint32_t v: x) {
            if (occcnt[v] == 0) {
                toClear.push_back(Lit(v, false));
            }

            //Don't roll around
            occcnt[v]++;
        }
    }

    for(const Lit c: toClear) {
        /*This is now possible because we don't XOR them together
        in case they clash on more than 1 variable */
        //assert(occcnt[c.var()] != 2);

        occcnt[c.var()] = 0;
    }
    toClear.clear();
    #endif

    return solver->okay();
}

void XorFinder::clean_xors_from_empty()
{
    size_t i2 = 0;
    for(size_t i = 0;i < xors.size(); i++) {
        Xor& x = xors[i];
        if (x.size() == 0
            && x.rhs == false
        ) {
            //nothing, skip
        } else {
            xors[i2] = xors[i];
            i2++;
        }
    }
    xors.resize(i2);
}

bool XorFinder::add_new_truths_from_xors(vector<Xor>& this_xors, vector<Lit>* out_changed_occur)
{
    size_t origTrailSize  = solver->trail_size();
    size_t origBins = solver->binTri.redBins;
    double myTime = cpuTime();

    assert(solver->ok);
    size_t i2 = 0;
    for(size_t i = 0;i < this_xors.size(); i++) {
        Xor& x = this_xors[i];
        solver->clean_xor_vars_no_prop(x.get_vars(), x.rhs);
        if (x.size() > 2) {
            this_xors[i2] = this_xors[i];
            i2++;
            continue;
        }

        switch(x.size() ) {
            case 0: {
                if (x.rhs == true) {
                    solver->ok = false;
                    return false;
                }
                break;
            }

            case 1: {
                Lit lit = Lit(x[0], !x.rhs);
                if (solver->value(lit) == l_False) {
                    solver->ok = false;
                } else if (solver->value(lit) == l_Undef) {
                    solver->enqueue(lit);
                    if (out_changed_occur)
                        solver->ok = solver->propagate_occur();
                    else
                        solver->ok = solver->propagate<true>().isNULL();
                }
                if (!solver->ok) {
                    goto end;
                }
                break;
            }

            case 2: {
                //RHS == 1 means both same is not allowed
                vector<Lit> lits{Lit(x[0], false), Lit(x[1], true^x.rhs)};
                solver->add_clause_int(lits, true, ClauseStats(), out_changed_occur != NULL);
                if (!solver->ok) {
                    goto end;
                }
                lits = {Lit(x[0], true), Lit(x[1], false^x.rhs)};
                solver->add_clause_int(lits, true, ClauseStats(), out_changed_occur != NULL);
                if (!solver->ok) {
                    goto end;
                }
                if (out_changed_occur) {
                    solver->ok = solver->propagate_occur();
                } else {
                    solver->ok = solver->propagate<true>().isNULL();
                }

                if (out_changed_occur) {
                    out_changed_occur->push_back(Lit(x[0], false));
                    out_changed_occur->push_back(Lit(x[1], false));
                }
                break;
            }

            default: {
                assert(false && "Not possible");
            }
        }
    }
    this_xors.resize(i2);
    end:

    double add_time = cpuTime() - myTime;
    uint32_t num_bins_added = solver->binTri.redBins - origBins;
    uint32_t num_units_added = solver->trail_size() - origTrailSize;

    if (solver->conf.verbosity) {
        cout
        << "c [xor-add-lem] added unit " << num_units_added
        << " bin " << num_bins_added
        << solver->conf.print_times(add_time)
        << endl;
    }


    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "xor-add-new-bin-unit"
            , add_time
        );
    }

    return solver->okay();
}

vector<uint32_t> XorFinder::xor_two(Xor& x1, Xor& x2, uint32_t& clash_num)
{
    clash_num = 0;
    x1.sort();
    x2.sort();
    vector<uint32_t> ret;
    size_t x1_at = 0;
    size_t x2_at = 0;
    while(x1_at < x1.size() || x2_at < x2.size()) {
        if (x1_at == x1.size()) {
            ret.push_back(x2[x2_at]);
            x2_at++;
            continue;
        }

        if (x2_at == x2.size()) {
            ret.push_back(x1[x1_at]);
            x1_at++;
            continue;
        }

        const uint32_t a = x1[x1_at];
        const uint32_t b = x2[x2_at];
        if (a == b) {
            clash_num++;
            x1_at++;
            x2_at++;
            continue;
        }

        if (a < b) {
            ret.push_back(a);
            x1_at++;
            continue;
        } else {
            ret.push_back(b);
            x2_at++;
            continue;
        }
    }

    return ret;
}

bool XorFinder::xor_has_interesting_var(const Xor& x)
{
    for(uint32_t v: x) {
        if (solver->seen[v] > 1) {
            return true;
        }
    }
    return false;
}

size_t XorFinder::mem_used() const
{
    size_t mem = 0;
    mem += xors.capacity()*sizeof(Xor);

    //Temporary
    mem += tmpClause.capacity()*sizeof(Lit);
    mem += varsMissing.capacity()*sizeof(uint32_t);

    return mem;
}

void XorFinder::grab_mem()
{
    occcnt.clear();
    occcnt.resize(solver->nVars(), 0);
}

void XorFinder::free_mem()
{
    occcnt.clear();
    occcnt.shrink_to_fit();
}

void XorFinder::Stats::print_short(const Solver* solver, double time_remain) const
{
    cout
    << "c [occ-xor] found " << std::setw(6) << foundXors
    << " avg sz " << std::setw(4) << std::fixed << std::setprecision(1)
    << float_div(sumSizeXors, foundXors)
    << solver->conf.print_times(findTime, time_outs, time_remain)
    << endl;
}

void XorFinder::Stats::print() const
{
    cout << "c --------- XOR STATS ----------" << endl;
    print_stats_line("c num XOR found on avg"
        , float_div(foundXors, numCalls)
        , "avg size"
    );

    print_stats_line("c XOR avg size"
        , float_div(sumSizeXors, foundXors)
    );

    print_stats_line("c XOR finding time"
        , findTime
        , float_div(time_outs, numCalls)*100.0
        , "time-out"
    );
    cout << "c --------- XOR STATS END ----------" << endl;
}

XorFinder::Stats& XorFinder::Stats::operator+=(const XorFinder::Stats& other)
{
    //Time
    findTime += other.findTime;

    //XOR
    foundXors += other.foundXors;
    sumSizeXors += other.sumSizeXors;

    //Usefulness
    time_outs += other.time_outs;

    return *this;
}

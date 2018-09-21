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

#include "clausecleaner.h"
#include "clauseallocator.h"
#include "solver.h"
#include "cryptominisat5/solvertypesmini.h"

using namespace CMSat;

//#define DEBUG_CLEAN
//#define VERBOSE_DEBUG

ClauseCleaner::ClauseCleaner(Solver* _solver) :
    solver(_solver)
{
}

bool ClauseCleaner::satisfied(const Watched& watched, Lit lit)
{
    assert(watched.isBin());
    if (solver->value(lit) == l_True) return true;
    if (solver->value(watched.lit2()) == l_True) return true;
    return false;
}

void ClauseCleaner::clean_binary_implicit(
    Watched& ws
    , Watched*& j
    , const Lit lit
) {
    if (satisfied(ws, lit)) {
        //Only delete once
        if (lit < ws.lit2()) {
            (*solver->drat) << del << lit << ws.lit2() << fin;
        }

        if (ws.red()) {
            impl_data.remLBin++;
        } else {
            impl_data.remNonLBin++;
        }
    } else {
        assert(solver->value(ws.lit2()) == l_Undef);
        assert(solver->value(lit) == l_Undef);
        *j++ = ws;
    }
}

void ClauseCleaner::clean_implicit_watchlist(
    watch_subarray& watch_list
    , const Lit lit
) {
    Watched* i = watch_list.begin();
    Watched* j = i;
    for (Watched* end2 = watch_list.end(); i != end2; i++) {
        if (i->isClause()) {
            *j++ = *i;
            continue;
        }

        if (i->isBin()) {
            clean_binary_implicit(*i, j, lit);
            continue;
        }
    }
    watch_list.shrink_(i - j);
}

void ClauseCleaner::clean_implicit_clauses()
{
    if (solver->conf.verbosity > 15) {
        cout << "c cleaning implicit clauses" << endl;
    }

    assert(solver->decisionLevel() == 0);
    impl_data = ImplicitData();
    size_t wsLit = 0;
    size_t wsLit2 = 2;
    for (size_t end = solver->watches.size()
        ; wsLit != end
        ; wsLit++, wsLit2++
    ) {
        if (wsLit2 < end
            && !solver->watches[Lit::toLit(wsLit2)].empty()
        ) {
            solver->watches.prefetch(Lit::toLit(wsLit2).toInt());
        }

        const Lit lit = Lit::toLit(wsLit);
        watch_subarray ws = solver->watches[lit];
        if (ws.empty())
            continue;

        clean_implicit_watchlist(ws, lit);
    }
    impl_data.update_solver_stats(solver);

    #ifdef DEBUG_IMPLICIT_STATS
    solver->check_implicit_stats();
    #endif
}

void ClauseCleaner::clean_clauses_inter(vector<ClOffset>& cs)
{
    assert(solver->decisionLevel() == 0);
    assert(solver->prop_at_head());

    if (solver->conf.verbosity > 15) {
        cout << "Cleaning clauses in vector<>" << endl;
    }

    vector<ClOffset>::iterator s, ss, end;
    size_t at = 0;
    for (s = ss = cs.begin(), end = cs.end();  s != end; ++s, ++at) {
        if (at + 1 < cs.size()) {
            Clause* pre_cl = solver->cl_alloc.ptr(cs[at+1]);
            __builtin_prefetch(pre_cl);
        }

        const ClOffset off = *s;
        Clause& cl = *solver->cl_alloc.ptr(off);

        const Lit origLit1 = cl[0];
        const Lit origLit2 = cl[1];
        const auto origSize = cl.size();
        const bool red = cl.red();

        if (clean_clause(cl)) {
            solver->watches.smudge(origLit1);
            solver->watches.smudge(origLit2);
            cl.setRemoved();
            if (red) {
                solver->litStats.redLits -= origSize;
            } else {
                solver->litStats.irredLits -= origSize;
            }
            delayed_free.push_back(off);
        } else {
            *ss++ = *s;
        }
    }
    cs.resize(cs.size() - (s-ss));
}

inline bool ClauseCleaner::clean_clause(Clause& cl)
{
    assert(cl.size() > 2);
    (*solver->drat) << deldelay << cl << fin;

    #ifdef SLOW_DEBUG
    uint32_t num_false_begin = 0;
    Lit l1 = cl[0];
    Lit l2 = cl[1];
    num_false_begin += solver->value(cl[0]) == l_False;
    num_false_begin += solver->value(cl[1]) == l_False;
    #endif

    Lit *i, *j, *end;
    uint32_t num = 0;
    for (i = j = cl.begin(), end = i + cl.size();  i != end; i++, num++) {
        lbool val = solver->value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }

        if (val == l_True) {
            (*solver->drat) << findelay;
            return true;
        }
    }
    if (i != j) {
        cl.shrink(i-j);
        (*solver->drat) << add << cl
        #ifdef STATS_NEEDED
        << solver->sumConflicts
        #endif
        << fin << findelay;
    } else {
        solver->drat->forget_delay();
    }

    assert(cl.size() > 1);
    assert(solver->value(cl[0]) == l_Undef);
    assert(solver->value(cl[1]) == l_Undef);

    #ifdef SLOW_DEBUG
    //no l_True, so first 2 of orig must have been l_Undef
    if (num_false_begin != 0) {
        cout << "val " << l1 << ":" << solver->value(l1) << endl;
        cout << "val " << l2 << ":" << solver->value(l2) << endl;
    }
    assert(num_false_begin == 0 && "Propagation wasn't full? Watch lit was l_False and clause wasn't satisfied");
    #endif

    if (i != j) {
        if (cl.size() == 2) {
            solver->attach_bin_clause(cl[0], cl[1], cl.red());
            return true;
        } else {
            if (cl.red()) {
                solver->litStats.redLits -= i-j;
            } else {
                solver->litStats.irredLits -= i-j;
            }
        }
    }

    return false;
}

bool ClauseCleaner::satisfied(const Clause& cl) const
{
    for (uint32_t i = 0; i != cl.size(); i++)
        if (solver->value(cl[i]) == l_True)
            return true;
    return false;
}

void ClauseCleaner::ImplicitData::update_solver_stats(Solver* solver)
{
    for(const BinaryClause& bincl: toAttach) {
        assert(solver->value(bincl.getLit1()) == l_Undef);
        assert(solver->value(bincl.getLit2()) == l_Undef);
        solver->attach_bin_clause(bincl.getLit1(), bincl.getLit2(), bincl.isRed());
    }

    assert(remNonLBin % 2 == 0);
    assert(remLBin % 2 == 0);
    solver->binTri.irredBins -= remNonLBin/2;
    solver->binTri.redBins -= remLBin/2;
}

void ClauseCleaner::clean_clauses_pre()
{
    assert(solver->watches.get_smudged_list().empty());
    assert(delayed_free.empty());
}

void ClauseCleaner::clean_clauses_post()
{
    solver->clean_occur_from_removed_clauses_only_smudged();
    for(ClOffset off: delayed_free) {
        solver->cl_alloc.clauseFree(off);
    }
    delayed_free.clear();
}

void ClauseCleaner::remove_and_clean_all()
{
    double myTime = cpuTime();
    assert(solver->okay());
    assert(solver->prop_at_head());

    clean_implicit_clauses();

    clean_clauses_pre();
    clean_clauses_inter(solver->longIrredCls);
    for(auto& lredcls: solver->longRedCls) {
        clean_clauses_inter(lredcls);
    }
    clean_clauses_post();


    #ifndef NDEBUG
    //Once we have cleaned the watchlists
    //no watchlist whose lit is set may be non-empty
    size_t wsLit = 0;
    for(watch_array::iterator
        it = solver->watches.begin(), end = solver->watches.end()
        ; it != end
        ; ++it, wsLit++
    ) {
        const Lit lit = Lit::toLit(wsLit);
        if (solver->value(lit) != l_Undef) {
            if (!it->empty()) {
                cout << "ERROR watches size: " << it->size() << endl;
                for(const auto& w: *it) {
                    cout << "ERROR w: " << w << endl;
                }
            }
            assert(it->empty());
        }
    }
    #endif

    if (solver->conf.verbosity >= 2) {
        cout
        << "c [clean] T: "
        << std::fixed << std::setprecision(4)
        << (cpuTime() - myTime)
        << " s" << endl;
    }
}


bool ClauseCleaner::clean_one_xor(Xor& x)
{
    bool rhs = x.rhs;
    size_t i = 0;
    size_t j = 0;
    for(size_t size = x.size(); i < size; i++) {
        uint32_t var = x[i];
        if (solver->value(var) != l_Undef) {
            rhs ^= solver->value(var) == l_True;
        } else {
            x[j++] = var;
        }
    }
    x.resize(j);
    x.rhs = rhs;

    switch(x.size()) {
        case 0:
            solver->ok &= !x.rhs;
            return false;

        case 1: {
            solver->fully_enqueue_this(Lit(x[0], !x.rhs));
            return false;
        }
        case 2: {
            solver->add_xor_clause_inter(vars_to_lits(x), x.rhs, true);
            return false;
        }
        default: {
            return true;
        }
    }
}

bool ClauseCleaner::clean_xor_clauses(vector<Xor>& xors)
{
    assert(solver->ok);
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ") Cleaning gauss clauses" << endl;
    for(Xor& x : xors) {
        cout << "orig XOR: " << x << endl;
    }
    #endif

    size_t last_trail = std::numeric_limits<size_t>::max();
    while(last_trail != solver->trail_size()) {
        last_trail = solver->trail_size();
        size_t i = 0;
        size_t j = 0;
        for(size_t size = xors.size(); i < size; i++) {
            Xor& x = xors[i];
            const bool keep = clean_one_xor(x);
            if (!solver->ok) {
                return false;
            }

            if (keep) {
                xors[j++] = x;
            }
        }
        xors.resize(j);

        #ifdef VERBOSE_DEBUG
        for(Xor& x : xors) {
            cout << "cleaned XOR: " << x << endl;
        }
        #endif
    }
    return solver->okay();
}

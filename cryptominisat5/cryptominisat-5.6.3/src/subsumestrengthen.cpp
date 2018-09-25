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

#include "subsumestrengthen.h"
#include "occsimplifier.h"
#include "solver.h"
#include "watchalgos.h"
#include "clauseallocator.h"
#include "sqlstats.h"
#include "solver.h"
#include "solvertypes.h"
#include "subsumeimplicit.h"
#include <array>

//#define VERBOSE_DEBUG

using namespace CMSat;

SubsumeStrengthen::SubsumeStrengthen(
    OccSimplifier* _simplifier
    , Solver* _solver
) :
    simplifier(_simplifier)
    , solver(_solver)
{
}

uint32_t SubsumeStrengthen::subsume_and_unlink_and_markirred(const ClOffset offset)
{
    Clause& cl = *solver->cl_alloc.ptr(offset);
    assert(!cl.getRemoved());
    assert(!cl.freed());

    #ifdef VERBOSE_DEBUG
    cout << "subsume-ing with clause: " << cl << endl;
    #endif

    Sub0Ret ret = subsume_and_unlink(
        offset
        , cl
        , cl.abst
    );

    //If irred is subsumed by redundant, make the redundant into irred
    if (cl.red()
        && ret.subsumedIrred
    ) {
        cl.makeIrred();
        solver->litStats.redLits -= cl.size();
        solver->litStats.irredLits += cl.size();
        if (!cl.getOccurLinked()) {
            simplifier->linkInClause(cl);
        } else {
            for(const Lit l: cl) {
                simplifier->n_occurs[l.toInt()]++;
            }
        }
    }

    //Combine stats
    cl.combineStats(ret.stats);

    return ret.numSubsumed;
}
template SubsumeStrengthen::Sub0Ret SubsumeStrengthen::subsume_and_unlink(
    const ClOffset offset
    , const vector<Lit>& ps
    , const cl_abst_type abs
    , const bool removeImplicit
);

uint32_t SubsumeStrengthen::backw_sub_long_with_implicit(
    const vector<Lit>& lits
) {
    Sub0Ret ret = subsume_and_unlink(
        CL_OFFSET_MAX
        , lits
        , calcAbstraction(lits)
        , false
    );
    return ret.numSubsumed;
}

/**
@brief Backward-subsumption using given clause
*/
template<class T>
SubsumeStrengthen::Sub0Ret SubsumeStrengthen::subsume_and_unlink(
    const ClOffset offset
    , const T& ps
    , const cl_abst_type abs
    , const bool removeImplicit
) {
    Sub0Ret ret;

    subs.clear();
    find_subsumed(offset, ps, abs, subs, removeImplicit);

    //Go through each clause that can be subsumed
    for (const ClOffset offs: subs) {
        Clause *tmp = solver->cl_alloc.ptr(offs);
        ret.stats = ClauseStats::combineStats(tmp->stats, ret.stats);
        #ifdef VERBOSE_DEBUG
        cout << "-> subsume removing:" << *tmp << endl;
        #endif

        if (!tmp->red()) {
            ret.subsumedIrred = true;
        }

        simplifier->unlink_clause(offs, true, false, true);
        ret.numSubsumed++;

        //If we are waaay over time, just exit
        if (*simplifier->limit_to_decrease < -20LL*1000LL*1000LL)
            break;
    }

    return ret;
}

SubsumeStrengthen::Sub1Ret SubsumeStrengthen::strengthen_subsume_and_unlink_and_markirred(const ClOffset offset)
{
    subs.clear();
    subsLits.clear();
    Sub1Ret ret;
    Clause& cl = *solver->cl_alloc.ptr(offset);
    assert(!cl.getRemoved());
    assert(!cl.freed());

    if (solver->conf.verbosity >= 6)
        cout << "strengthen_subsume_and_unlink_and_markirred-ing with clause:" << cl << endl;

    findStrengthened(
        offset
        , cl
        , cl.abst
        , subs
        , subsLits
    );

    for (size_t j = 0
        ; j < subs.size() && solver->okay()
        ; j++
    ) {
        ClOffset offset2 = subs[j];
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        #ifdef USE_GAUSS
        if (cl2.used_in_xor()) {
            continue;
        }
        #endif

        if (subsLits[j] == lit_Undef) {  //Subsume
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6)
                cout << "subsumed clause " << cl2 << endl;
            #endif

            //If subsumes a irred, and is redundant, make it irred
            if (cl.red()
                && !cl2.red()
            ) {
                cl.makeIrred();
                solver->litStats.redLits -= cl.size();
                solver->litStats.irredLits += cl.size();
                if (!cl.getOccurLinked()) {
                    simplifier->linkInClause(cl);
                } else {
                    for(const Lit l: cl) {
                        simplifier->n_occurs[l.toInt()]++;
                    }
                }
            }

            //Update stats
            cl.combineStats(cl2.stats);

            simplifier->unlink_clause(offset2, true, false, true);
            ret.sub++;
        } else { //Strengthen
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6) {
                cout << "strenghtened clause " << cl2 << endl;
            }
            #endif
            #ifdef USE_GAUSS
            if (cl2.used_in_xor()) {
                continue;
            }
            #endif
            remove_literal(offset2, subsLits[j]);

            ret.str++;
            if (!solver->ok)
                return ret;

            //If we are waaay over time, just exit
            if (*simplifier->limit_to_decrease < -20LL*1000LL*1000LL)
                break;
        }
    }

    return ret;
}

void SubsumeStrengthen::randomise_clauses_order()
{
    const size_t sz = simplifier->clauses.size();
    for (size_t i = 0
        ; i + 1 < sz
        ; i++
    ) {
        std::swap(
            simplifier->clauses[i]
            , simplifier->clauses[i+solver->mtrand.randInt(simplifier->clauses.size()-1-i)]
        );
    }
}

void SubsumeStrengthen::backw_sub_long_with_long()
{
    //If clauses are empty, the system below segfaults
    if (simplifier->clauses.empty())
        return;

    double myTime = cpuTime();
    size_t wenThrough = 0;
    size_t subsumed = 0;
    const int64_t orig_limit = simplifier->subsumption_time_limit;
    randomise_clauses_order();
    while (*simplifier->limit_to_decrease > 0
        && (double)wenThrough < solver->conf.subsume_gothrough_multip*(double)simplifier->clauses.size()
    ) {
        *simplifier->limit_to_decrease -= 3;
        wenThrough++;

        //Print status
        if (solver->conf.verbosity >= 5
            && wenThrough % 10000 == 0
        ) {
            cout << "toDecrease: " << *simplifier->limit_to_decrease << endl;
        }

        const size_t at = wenThrough % simplifier->clauses.size();
        const ClOffset offset = simplifier->clauses[at];
        Clause* cl = solver->cl_alloc.ptr(offset);

        //Has already been removed
        if (cl->freed() || cl->getRemoved())
            continue;


        *simplifier->limit_to_decrease -= 10;
        subsumed += subsume_and_unlink_and_markirred(offset);
    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = (*simplifier->limit_to_decrease <= 0);
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_limit);
    if (solver->conf.verbosity) {
        cout
        << "c [occ-sub-long-w-long] rem cl: " << subsumed
        << " tried: " << wenThrough << "/" << simplifier->clauses.size()
        << " (" << std::setprecision(1) << std::fixed
        << stats_line_percent(wenThrough, simplifier->clauses.size())
        << "%)"
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-sub-long-w-long"
            , time_used
            , time_out
            , time_remain
        );
    }

    //Update time used
    runStats.subsumedBySub += subsumed;
    runStats.subsumeTime += cpuTime() - myTime;
}

bool SubsumeStrengthen::backw_str_long_with_long()
{
    assert(solver->ok);

    double myTime = cpuTime();
    size_t wenThrough = 0;
    const int64_t orig_limit = *simplifier->limit_to_decrease;
    Sub1Ret ret;

    randomise_clauses_order();
    while(*simplifier->limit_to_decrease > 0
        && wenThrough < 1.5*(double)2*simplifier->clauses.size()
        && solver->okay()
    ) {
        *simplifier->limit_to_decrease -= 10;
        wenThrough++;

        //Print status
        if (solver->conf.verbosity >= 5
            && wenThrough % 10000 == 0
        ) {
            cout << "toDecrease: " << *simplifier->limit_to_decrease << endl;
        }

        const size_t at = wenThrough % simplifier->clauses.size();
        ClOffset offset = simplifier->clauses[at];
        Clause* cl = solver->cl_alloc.ptr(offset);

        //Has already been removed
        if (cl->freed() || cl->getRemoved())
            continue;

        ret += strengthen_subsume_and_unlink_and_markirred(offset);

    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = *simplifier->limit_to_decrease <= 0;
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_limit);

    if (solver->conf.verbosity) {
        cout
        << "c [occ-sub-str-long-w-long] sub: " << ret.sub
        << " str: " << ret.str
        << " tried: " << wenThrough << "/" << simplifier->clauses.size()
        << " ("
        << stats_line_percent(wenThrough, simplifier->clauses.size())
        << ") "
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-sub-str-long-w-long"
            , time_used
            , time_out
            , time_remain
        );
    }

    //Update time used
    runStats.subsumedByStr += ret.sub;
    runStats.litsRemStrengthen += ret.str;
    runStats.strengthenTime += cpuTime() - myTime;

    return solver->okay();
}

/**
@brief Helper function for findStrengthened

Used to avoid duplication of code
*/
template<class T>
void inline SubsumeStrengthen::fillSubs(
    const ClOffset offset
    , const T& cl
    , const cl_abst_type abs
    , vector<ClOffset>& out_subsumed
    , vector<Lit>& out_lits
    , const Lit lit
) {
    Lit litSub;
    watch_subarray_const cs = solver->watches[lit];
    *simplifier->limit_to_decrease -= (long)cs.size()*2+ 40;
    for (const Watched *it = cs.begin(), *end = cs.end()
        ; it != end
        ; ++it
    ) {
        if (!it->isClause())
            continue;

        if (it->get_offset() == offset
            || !subsetAbst(abs, it->getAbst())
        ) {
            continue;
        }

        ClOffset offset2 = it->get_offset();
        const Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (cl2.getRemoved()
            || cl.size() > cl2.size())
        {
            continue;
        }

        *simplifier->limit_to_decrease -= (long)((cl.size() + cl2.size())/4);
        litSub = subset1(cl, cl2);
        if (litSub != lit_Error) {
            out_subsumed.push_back(it->get_offset());
            out_lits.push_back(litSub);

            #ifdef VERBOSE_DEBUG
            if (litSub == lit_Undef) cout << "subsume-d: ";
            else cout << "strengthen_subsume_and_unlink_and_markirred-ed (lit: "
                << litSub
                << ") clause offset: "
                << it->get_offset()
                << endl;
            #endif
        }
    }
}

/**
@brief Checks if clauses are subsumed or could be strenghtened with given clause

Checks if:
* any clause is subsumed with given clause
* the given clause could perform self-subsuming resolution on any other clause

@param[in] ps The clause to perform the above listed algos with
@param[in] abs The abstraction of clause ps
@param[out] out_subsumed The clauses that could be modified by ps
@param[out] out_lits Defines HOW these clauses could be modified. By removing
literal, or by subsumption (in this case, there is lit_Undef here)
*/
template<class T>
void SubsumeStrengthen::findStrengthened(
    ClOffset offset
    , const T& cl
    , const cl_abst_type abs
    , vector<ClOffset>& out_subsumed
    , vector<Lit>& out_lits
)
{
    #ifdef VERBOSE_DEBUG
    cout << "findStrengthened: " << cl << endl;
    #endif

    uint32_t minVar = var_Undef;
    uint32_t bestSize = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < cl.size(); i++){
        uint32_t newSize =
            solver->watches[cl[i]].size()
                + solver->watches[~cl[i]].size();

        if (newSize < bestSize) {
            minVar = cl[i].var();
            bestSize = newSize;
        }
    }
    assert(minVar != var_Undef);
    *simplifier->limit_to_decrease -= (long)cl.size();

    fillSubs(offset, cl, abs, out_subsumed, out_lits, Lit(minVar, true));
    fillSubs(offset, cl, abs, out_subsumed, out_lits, Lit(minVar, false));
}

bool SubsumeStrengthen::handle_added_long_cl(
    int64_t* limit_to_decrease, const bool main_run)
{
    int64_t orig_limit = *limit_to_decrease;
    size_t origTrailSize = solver->trail_size();
    const double start_time = cpuTime();
    Sub1Ret stat;
    bool interrupted = false;

    //NOTE added_long_cl CAN CHANGE while the below is running!
    for(size_t i = 0
        ; i < simplifier->added_long_cl.size()
        && *simplifier->limit_to_decrease >= 0
        ; i++
    ) {
        const ClOffset offs = simplifier->added_long_cl[i];
        Clause* cl = solver->cl_alloc.ptr(offs);
        if (cl->freed() || cl->getRemoved())
            continue;

        cl->stats.marked_clause = 0;
        auto ret = strengthen_subsume_and_unlink_and_markirred(offs);
        stat += ret;
        if (!solver->ok) {
            goto end;
        }

        if ((i&0xfff) == 0xfff
            && solver->must_interrupt_asap()
        ) {
            interrupted = true;
            goto end;
        }
    }
    if (*simplifier->limit_to_decrease < 0) {
        interrupted = true;
    }

    end:

    //we still have to clear the marks
    if (interrupted) {
        for(const ClOffset offs: simplifier->added_long_cl) {
            Clause* cl = solver->cl_alloc.ptr(offs);
            if (cl->freed() || cl->getRemoved())
                continue;

            cl->stats.marked_clause = 0;
        }
    }

    if (main_run) {
        const bool time_out =  *limit_to_decrease <= 0;
        const double time_used = cpuTime() - start_time;
        const double time_remain = float_div(*limit_to_decrease, orig_limit);
        if (solver->conf.verbosity) {
            cout
            << "c [occ-sub-str-w-added-long] "
            << " sub: " << stat.sub
            << " str: " << stat.str
            << " 0-depth ass: " << solver->trail_size() - origTrailSize
            << solver->conf.print_times(time_used, time_out, time_remain)
            << endl;
        }
        if (solver->sqlStats) {
            solver->sqlStats->time_passed(
                solver
                , "occ-sub-str-w-added-long"
                , time_used
                , time_out
                , time_remain
            );
        }
    }

    return solver->okay();
}

void SubsumeStrengthen::remove_literal(ClOffset offset, const Lit toRemoveLit)
{
    Clause& cl = *solver->cl_alloc.ptr(offset);
    #ifdef VERBOSE_DEBUG
    cout << "-> Strenghtening clause :" << cl;
    cout << " with lit: " << toRemoveLit << endl;
    #endif

    *simplifier->limit_to_decrease -= 5;

    (*solver->drat) << deldelay << cl << fin;
    cl.strengthen(toRemoveLit);
    simplifier->added_cl_to_var.touch(toRemoveLit.var());
    cl.recalc_abst_if_needed();
    (*solver->drat) << add << cl
    #ifdef STATS_NEEDED
    << solver->sumConflicts
    #endif
    << fin << findelay;
    if (!cl.red()) {
        simplifier->n_occurs[toRemoveLit.toInt()]--;
        simplifier->elim_calc_need_update.touch(toRemoveLit.var());
        simplifier->removed_cl_with_var.touch(toRemoveLit.var());
    }

    runStats.litsRemStrengthen++;
    removeWCl(solver->watches[toRemoveLit], offset);
    if (cl.red())
        solver->litStats.redLits--;
    else
        solver->litStats.irredLits--;

    simplifier->clean_clause(offset);
}
/**
@brief Decides only using abstraction if clause A could subsume clause B

@note: It can give false positives. Never gives false negatives.

For A to subsume B, everything that is in A MUST be in B. So, if (A & ~B)
contains even one bit, it means that A contains something that B doesn't. So
A may be a subset of B only if (A & ~B) == 0
*/
bool SubsumeStrengthen::subsetAbst(const cl_abst_type A, const cl_abst_type B)
{
    return ((A & ~B) == 0);
}

//A subsumes B (A <= B)
template<class T1, class T2>
bool SubsumeStrengthen::subset(const T1& A, const T2& B)
{
    #ifdef MORE_DEUBUG
    cout << "A:" << A << endl;
    for(size_t i = 1; i < A.size(); i++) {
        assert(A[i-1] < A[i]);
    }

    cout << "B:" << B << endl;
    for(size_t i = 1; i < B.size(); i++) {
        assert(B[i-1] < B[i]);
    }
    #endif

    bool ret;
    uint32_t i = 0;
    uint32_t i2;
    Lit lastB = lit_Undef;
    for (i2 = 0; i2 < B.size(); i2++) {
        if (lastB != lit_Undef)
            assert(lastB < B[i2]);

        lastB = B[i2];
        //Literals are ordered
        if (A[i] < B[i2]) {
            ret = false;
            goto end;
        }
        else if (A[i] == B[i2]) {
            i++;

            //went through the whole of A now, so A subsumes B
            if (i == A.size()) {
                ret = true;
                goto end;
            }
        }
    }
    ret = false;

    end:
    *simplifier->limit_to_decrease -= (long)i2*4 + (long)i*4;
    return ret;
}

/**
@brief Decides if A subsumes B, or if not, if A could strenghten B

@note: Assumes 'seen' is cleared (will leave it cleared)

Helper function for strengthening. Does two things in one go:
1) decides if clause A could subsume clause B
2) decides if clause A could be used to perform self-subsuming resoltuion on
clause B

@return lit_Error, if neither (1) or (2) is true. Returns lit_Undef (1) is true,
and returns the literal to remove if (2) is true
*/
template<class T1, class T2>
Lit SubsumeStrengthen::subset1(const T1& A, const T2& B)
{
    Lit retLit = lit_Undef;

    uint32_t i = 0;
    uint32_t i2;
    for (i2 = 0; i2 < B.size(); i2++) {
        if (A[i] == ~B[i2] && retLit == lit_Undef) {
            retLit = B[i2];
            i++;
            if (i == A.size())
                goto end;

            continue;
        }

        //Literals are ordered
        if (A[i] < B[i2]) {
            retLit = lit_Error;
            goto end;
        }

        if (A[i] == B[i2]) {
            i++;

            if (i == A.size())
                goto end;
        }
    }
    retLit = lit_Error;

    end:
    *simplifier->limit_to_decrease -= (long)i2*4 + (long)i*4;
    return retLit;
}

template<class T>
size_t SubsumeStrengthen::find_smallest_watchlist_for_clause(const T& ps) const
{
    size_t min_i = 0;
    size_t min_num = solver->watches[ps[min_i]].size();
    for (uint32_t i = 1; i < ps.size(); i++){
        const size_t this_num = solver->watches[ps[i]].size();
        if (this_num < min_num) {
            min_i = i;
            min_num = this_num;
        }
    }
    *simplifier->limit_to_decrease -= (long)ps.size();

    return min_i;
}

/**
@brief Finds clauses that are backward-subsumed by given clause

Only handles backward-subsumption. Uses occurrence lists
@param[out] out_subsumed The set of clauses subsumed by the given
*/
template<class T> void SubsumeStrengthen::find_subsumed(
    const ClOffset offset //Will not match with index of the name value
    , const T& ps //Literals in clause
    , const cl_abst_type abs //Abstraction of literals in clause
    , vector<ClOffset>& out_subsumed //List of clause indexes subsumed
    , bool removeImplicit
) {
    #ifdef VERBOSE_DEBUG
    cout << "find_subsumed: ";
    for (const Lit lit: ps) {
        cout << lit << " , ";
    }
    cout << endl;
    #endif

    const size_t smallest = find_smallest_watchlist_for_clause(ps);

    //Go through the occur list of the literal that has the smallest occur list
    watch_subarray occ = solver->watches[ps[smallest]];
    *simplifier->limit_to_decrease -= (long)occ.size()*8 + 40;

    Watched* it = occ.begin();
    Watched* it2 = occ.begin();
    size_t numBinFound = 0;
    for (const Watched* end = occ.end()
        ; it != end
        ; ++it
    ) {
        if (removeImplicit) {
            if (it->isBin()
                && ps.size() == 2
                && ps[!smallest] == it->lit2()
                && !it->red()
            ) {
                /*cout
                << "ps " << ps << " could subsume this bin: "
                << ps[smallest] << ", " << it->lit2()
                << endl;*/
                numBinFound++;

                //We cannot remove ourselves
                if (numBinFound > 1) {
                    removeWBin(solver->watches, it->lit2(), ps[smallest], it->red());
                    solver->binTri.irredBins--;
                    continue;
                }
            }
        }
        *it2++ = *it;

        if (!it->isClause()) {
            continue;
        }

        *simplifier->limit_to_decrease -= 15;

        if (it->get_offset() == offset
            || !subsetAbst(abs, it->getAbst())
        ) {
            continue;
        }

        const ClOffset offset2 = it->get_offset();
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);

        if (ps.size() > cl2.size() || cl2.getRemoved())
            continue;

        *simplifier->limit_to_decrease -= 50;
        if (subset(ps, cl2)) {
            out_subsumed.push_back(offset2);
            #ifdef VERBOSE_DEBUG
            cout << "subsumed cl offset: " << offset2 << endl;
            #endif
        }
    }
    occ.shrink(it-it2);
}
template void SubsumeStrengthen::find_subsumed(
    const ClOffset offset
    , const std::array<Lit, 2>& ps
    , const cl_abst_type abs //Abstraction of literals in clause
    , vector<ClOffset>& out_subsumed //List of clause indexes subsumed
    , bool removeImplicit
);

size_t SubsumeStrengthen::mem_used() const
{
    size_t b = 0;
    b += subs.capacity()*sizeof(ClOffset);
    b += subsLits.capacity()*sizeof(Lit);

    return b;
}

void SubsumeStrengthen::finishedRun()
{
    globalstats += runStats;
}

void SubsumeStrengthen::Stats::print_short(const Solver* solver) const
{
    cout << "c [subs] long"
    << " subBySub: " << subsumedBySub
    << " subByStr: " << subsumedByStr
    << " lits-rem-str: " << litsRemStrengthen
    << solver->conf.print_times(subsumeTime+strengthenTime)
    << endl;
}

void SubsumeStrengthen::Stats::print() const
{
    cout << "c -------- SubsumeStrengthen STATS ----------" << endl;
    print_stats_line("c cl-subs"
        , subsumedBySub + subsumedByStr
        , " Clauses"
    );
    print_stats_line("c cl-str rem lit"
        , litsRemStrengthen
        , " Lits"
    );
    print_stats_line("c cl-sub T"
        , subsumeTime
        , " s"
    );
    print_stats_line("c cl-str T"
        , strengthenTime
        , " s"
    );
    cout << "c -------- SubsumeStrengthen STATS END ----------" << endl;
}

SubsumeStrengthen::Stats& SubsumeStrengthen::Stats::operator+=(const Stats& other)
{
    subsumedBySub += other.subsumedBySub;
    subsumedByStr += other.subsumedByStr;
    litsRemStrengthen += other.litsRemStrengthen;

    subsumeTime += other.subsumeTime;
    strengthenTime += other.strengthenTime;

    return *this;
}

SubsumeStrengthen::Sub1Ret SubsumeStrengthen::backw_sub_str_long_with_implicit(
    const vector<Lit>& lits
) {
    subs.clear();
    subsLits.clear();

    findStrengthened(
        CL_OFFSET_MAX
        , lits
        , calcAbstraction(lits)
        , subs
        , subsLits
    );

    Sub1Ret ret;

    for (size_t j = 0
        ; j < subs.size() && solver->okay()
        ; j++
    ) {
        ClOffset offset2 = subs[j];
        Clause& cl2 = *solver->cl_alloc.ptr(offset2);
        if (subsLits[j] == lit_Undef) {  //Subsume
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6)
                cout << "subsumed clause " << cl2 << endl;
            #endif
            #ifdef USE_GAUSS
            if (cl2.used_in_xor()) {
                continue;
            }
            #endif

            if (!cl2.red()) {
                ret.subsumedIrred = true;
            }

            simplifier->unlink_clause(offset2, true, false, true);
            ret.sub++;
        } else { //Strengthen
            #ifdef VERBOSE_DEBUG
            if (solver->conf.verbosity >= 6) {
                cout << "strenghtened clause " << cl2 << endl;
            }
            #endif
            #ifdef USE_GAUSS
            if (cl2.used_in_xor()) {
                //cout << "str-ing used in XOR with bin" << endl;
                continue;
            }
            #endif
            remove_literal(offset2, subsLits[j]);

            ret.str++;
            if (!solver->ok)
                return ret;

            //If we are waaay over time, just exit
            if (*simplifier->limit_to_decrease < -20LL*1000LL*1000LL)
                break;
        }
    }

    return ret;
}

bool SubsumeStrengthen::backw_sub_str_long_with_bins_watch(
    const Lit lit
    , const bool redundant_too
) {
    watch_subarray ws = solver->watches[lit];
    for (size_t i = 0
        ; i < ws.size() && *simplifier->limit_to_decrease > 0
        ; i++
    ) {
        //Each BIN only once
        if (ws[i].isBin()
            && (redundant_too || lit < ws[i].lit2())
        ) {
            const bool red = ws[i].red();
            tried_bin_tri++;
            tmpLits.resize(2);
            tmpLits[0] = lit;
            tmpLits[1] = ws[i].lit2();
            std::sort(tmpLits.begin(), tmpLits.end());

            Sub1Ret ret = backw_sub_str_long_with_implicit(tmpLits);
            subsumedBin += ret.sub;
            strBin += ret.str;
            if (!solver->ok)
                return false;

            if (red
                && ret.subsumedIrred
            ) {
                solver->binTri.redBins--;
                solver->binTri.irredBins++;
                simplifier->n_occurs[tmpLits[0].toInt()]++;
                simplifier->n_occurs[tmpLits[1].toInt()]++;
                findWatchedOfBin(solver->watches, tmpLits[1], tmpLits[0], true).setRed(false);
                findWatchedOfBin(solver->watches, tmpLits[0], tmpLits[1], true).setRed(false);
            }
            continue;
        }

        //Must be a longer clause, break
        //assert(ws[i].isClause());
        //break;
    }

    return true;
}

bool SubsumeStrengthen::backw_sub_str_long_with_bins()
{
    //Stats
    int64_t orig_time_limit = *simplifier->limit_to_decrease;
    const size_t origTrailSize = solver->trail_size();
    double myTime = cpuTime();
    subsumedBin = 0;
    strBin = 0;

    //Randomize start in the watchlist
    size_t upI;
    upI = solver->mtrand.randInt(solver->watches.size()-1);

    size_t numDone = 0;
    for (; numDone < solver->watches.size() && *simplifier->limit_to_decrease > 0
        ; upI = (upI +1) % solver->watches.size(), numDone++

    ) {
        Lit lit = Lit::toLit(upI);
        if (!backw_sub_str_long_with_bins_watch(lit, true)) {
            break;
        }
    }

    const double time_used = cpuTime() - myTime;
    const bool time_out = *simplifier->limit_to_decrease <= 0;
    const double time_remain = float_div(*simplifier->limit_to_decrease, orig_time_limit);
    if (solver->conf.verbosity) {
        cout
        << "c [occ-backw-sub-str-long-w-bins]"
        << " subs: " << subsumedBin
        << " str: " << strBin
        << " tried: " << tried_bin_tri
        << " 0-depth ass: " << solver->trail_size() - origTrailSize
        << solver->conf.print_times(time_used, time_out, time_remain)
        << endl;
    }

    if (solver->sqlStats) {
        solver->sqlStats->time_passed(
            solver
            , "occ-backw-sub-str-long-w-bins"
            , time_used
            , time_out
            , time_remain
        );
    }

    //runStats.zeroDepthAssigns = solver->trail_size() - origTrailSize;

    return solver->okay();
}


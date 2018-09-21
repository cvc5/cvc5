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

#include "implcache.h"

#ifndef TRANSCACHE_H_
#define TRANSCACHE_H_

#include "solver.h"
#include "varreplacer.h"
#include "varupdatehelper.h"
#include "time_mem.h"
#include "sqlstats.h"

using namespace CMSat;
using std::cout;
using std::endl;

//Make all literals as if propagated only by redundant
void ImplCache::makeAllRed()
{
    for(vector<TransCache>::iterator
        it = implCache.begin(), end = implCache.end()
        ; it != end
        ; ++it
    ) {
        it->makeAllRed();
    }
}

size_t ImplCache::mem_used() const
{
    double numBytes = 0;
    for(vector<TransCache>::const_iterator
        it = implCache.begin(), end = implCache.end()
        ; it != end
        ; ++it
    ) {
        //1.2 is overhead
        numBytes += (double)it->lits.capacity()*(double)sizeof(LitExtra)*1.2;
    }
    numBytes += implCache.capacity()*sizeof(vector<TransCache>);

    return numBytes;
}

void ImplCache::print_stats(const Solver* solver) const
{
    cout
    << "c --------- Implication Cache Stats Start ----------"
    << endl;

    print_statsSort(solver);

    cout
    << "c --------- Implication Cache Stats End   ----------"
    << endl;
}

void ImplCache::print_statsSort(const Solver* solver) const
{
    size_t numHasElems = 0;
    size_t totalElems = 0;
    size_t activeLits = 0;

    for(size_t i = 0; i < implCache.size(); i++) {
        Lit lit = Lit::toLit(i);

        if (solver->varData[lit.var()].removed == Removed::none) {
            activeLits++;
            totalElems += implCache[i].lits.size();
            numHasElems += !implCache[i].lits.empty();
        }
    }

    print_stats_line(
        "c lits having cache"
        , stats_line_percent(numHasElems, activeLits)
        , "% of decision lits"
    );

    print_stats_line(
        "c num elems in cache/lit"
        , stats_line_percent(totalElems, numHasElems)
        , "extralits"
    );
}

bool ImplCache::clean(Solver* solver, bool* setSomething)
{
    assert(solver->ok);
    assert(solver->decisionLevel() == 0);
    vector<Lit> toEnqueue;

    double myTime = cpuTime();
    uint64_t numUpdated = 0;
    uint64_t numCleaned = 0;
    uint64_t numFreed = 0;

    //Merge in & free memory
    for (uint32_t var = 0; var < solver->nVars(); var++) {

        //If replaced, merge it into the one that replaced it
        if (solver->varData[var].removed == Removed::replaced) {
            for(int i = 0; i < 2; i++) {
                const Lit litOrig = Lit(var, i);
                if (implCache[litOrig.toInt()].lits.empty())
                    continue;

                const Lit lit = solver->varReplacer->get_lit_replaced_with(litOrig);

                //Updated literal must be normal, otherwise, biig problems e.g
                //implCache is not even large enough, etc.
                if (solver->varData[lit.var()].removed == Removed::none) {
                    bool taut = implCache.at(lit.toInt()).merge(
                        implCache[litOrig.toInt()].lits
                        , lit_Undef //nothing to add
                        , false //replaced, so 'irred'
                        , lit.var() //exclude the literal itself
                        , solver->seen
                    );

                    if (taut) {
                        toEnqueue.push_back(lit);
                        (*solver->drat) << add << lit
                        #ifdef STATS_NEEDED
                        << solver->clauseID++
                        << solver->sumConflicts
                        #endif
                        << fin;
                    }
                }
            }
        }

        //Free it
        if (solver->value(var) != l_Undef
            || solver->varData[var].removed != Removed::none
        ) {
            vector<LitExtra> tmp1;
            numFreed += implCache[Lit(var, false).toInt()].lits.capacity();
            implCache[Lit(var, false).toInt()].lits.swap(tmp1);

            vector<LitExtra> tmp2;
            numFreed += implCache[Lit(var, true).toInt()].lits.capacity();
            implCache[Lit(var, true).toInt()].lits.swap(tmp2);
        }
    }

    vector<uint16_t>& inside = solver->seen;
    vector<uint8_t>& irred = solver->seen2;
    size_t wsLit = 0;
    for(vector<TransCache>::iterator
        trans = implCache.begin(), transEnd = implCache.end()
        ; trans != transEnd
        ; trans++, wsLit++
    ) {
        //Stats
        size_t origSize = trans->lits.size();
        size_t newSize = 0;

        //Update to replaced vars, remove vars already set or eliminated
        Lit vertLit = Lit::toLit(wsLit);
        for (vector<LitExtra>::iterator end = trans->lits.end(),
            it=trans->lits.begin(), it2 = trans->lits.begin()
            ; it != end
            ; ++it
        ) {
            Lit lit = it->getLit();
            assert(lit.var() != vertLit.var());

            //Remove if value is set
            if (solver->value(lit.var()) != l_Undef)
                continue;

            //Update to its replaced version
            if (solver->varData[lit.var()].removed == Removed::replaced) {
                lit = solver->varReplacer->get_lit_replaced_with(lit);

                //This would be tautological (and incorrect), so skip
                if (lit.var() == vertLit.var())
                    continue;
                numUpdated++;
            }

            //Yes, it's possible that the child was not set, but the parent is set
            //This is because there is a delay between replacement and cache cleaning
            if (solver->value(lit.var()) != l_Undef)
                continue;

            //If updated version is eliminated/decomposed, skip
            if (solver->varData[lit.var()].removed != Removed::none)
                continue;

            //Mark irred
            irred[lit.toInt()] |= (char)it->getOnlyIrredBin();

            //If we have already visited this var, just skip over, but update irred
            if (inside[lit.toInt()]) {
                continue;
            }

            inside[lit.toInt()] = true;
            *it2++ = LitExtra(lit, it->getOnlyIrredBin());
            newSize++;
        }
        trans->lits.resize(newSize);

        //Now that we have gone through the list, go through once more to:
        //1) set irred right (above we might have it set later)
        //2) clear 'inside'
        //3) clear 'irred'
        for (vector<LitExtra>::iterator
            it2 = trans->lits.begin(), end2 = trans->lits.end()
            ;it2 != end2
            ; it2++
        ) {
            Lit lit = it2->getLit();

            //Clear 'inside'
            inside[lit.toInt()] = false;

            //Clear 'irred'
            const bool nRed = irred[lit.toInt()];
            irred[lit.toInt()] = false;

            //Set non-leartness correctly
            *it2 = LitExtra(lit, nRed);
            assert(solver->varData[it2->getLit().var()].removed == Removed::none);
            assert(solver->value(it2->getLit()) == l_Undef);
        }
        numCleaned += origSize-trans->lits.size();
    }

    size_t origTrailDepth = solver->trail_size();
    solver->fully_enqueue_these(toEnqueue);
    if (setSomething) {
        *setSomething = (solver->trail_size() != origTrailDepth);
    }

    const double time_used = cpuTime()-myTime;
    if (solver->conf.verbosity) {
        cout << "c [cache] cleaned."
        << " Updated: " << std::setw(7) << numUpdated/1000 << " K"
        << " Cleaned: " << std::setw(7) << numCleaned/1000 << " K"
        << " Freed: " << std::setw(7) << numFreed/1000 << " K"
        << solver->conf.print_times(time_used)
        << endl;
    }
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "clean cache"
            , time_used
        );
    }

    return solver->okay();
}

void ImplCache::handleNewData(
    vector<uint8_t>& val
    , uint32_t var
    , Lit lit
) {
    //Unfortunately, we cannot add the clauses, because that could mess up
    //the watchlists, which are being traversed by the callers, so we add these
    //new truths as delayed clauses, and add them at the end

    //a->b and (-a)->b, so 'b'
    if  (val[lit.var()] == lit.sign()) {
        delayedClausesToAddNorm.push_back(lit);
        runStats.bProp++;
    } else {
        //a->b, and (-a)->(-b), so equivalent literal
        auto tmp = std::make_pair(Lit(var, false), Lit(lit.var(), false));
        bool sign = lit.sign();
        delayedClausesToAddXor.push_back(std::make_pair(tmp, sign));
        runStats.bXProp++;
    }
}

bool ImplCache::addDelayedClauses(Solver* solver)
{
    assert(solver->ok);
    vector<Lit> tmp;

    //Add all delayed clauses
    if (solver->conf.doFindAndReplaceEqLits) {
        for(const auto& x: delayedClausesToAddXor) {
            Lit lit1 = x.first.first;
            Lit lit2 = x.first.second;
            if (solver->varData[lit1.var()].removed != Removed::none ||
                solver->varData[lit2.var()].removed != Removed::none
            ) {
                //Var has been eliminated one way or another. Don't add this clause
                continue;
            }

            //Add the clause
            tmp.clear();
            tmp.push_back(lit1);
            tmp.push_back(lit2);
            solver->add_xor_clause_inter(tmp, x.second, true);

            //Check if this caused UNSAT
            if  (!solver->ok)
                return false;
        }
    }

    for(vector<Lit>::const_iterator
        it = delayedClausesToAddNorm.begin(), end = delayedClausesToAddNorm.end()
        ; it != end
        ; ++it
    ) {
        //Build unit clause
        tmp.resize(1);
        tmp[0] = *it;

        //Add unit clause
        solver->add_clause_int(tmp);

        //Check if this caused UNSAT
        if  (!solver->ok)
            return false;
    }

    //Clear all
    delayedClausesToAddXor.clear();
    delayedClausesToAddNorm.clear();

    return true;
}

bool ImplCache::tryBoth(Solver* solver)
{
    assert(solver->ok);
    assert(solver->decisionLevel() == 0);
    const size_t origTrailSize = solver->trail_size();
    runStats.clear();
    runStats.numCalls = 1;

    //Measuring time & usefulness
    double myTime = cpuTime();

    for (uint32_t var = 0; var < solver->nVars(); var++) {

        //If value is set or eliminated, skip
        if (solver->value(var) != l_Undef
            || solver->varData[var].removed != Removed::none
        ) {
            continue;
        }

        //Try to do it
        tryVar(solver, var);

        //Add all clauses that have been delayed
        if (!addDelayedClauses(solver))
            goto end;
    }

end:
    const double time_used = cpuTime() - myTime;
    runStats.zeroDepthAssigns = solver->trail_size() - origTrailSize;
    runStats.cpu_time = time_used;
    if (solver->conf.verbosity) {
        runStats.print_short(solver);
    }
    globalStats += runStats;
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "cache extractboth"
            , time_used
        );
    }

    return solver->okay();
}

void ImplCache::tryVar(
    Solver* solver
    , uint32_t var
) {
    //Sanity check
    assert(solver->ok);
    assert(solver->decisionLevel() == 0);

    //Convenience
    vector<uint16_t>& seen = solver->seen;
    vector<uint8_t>& val = solver->seen2;

    Lit lit = Lit(var, false);

    const vector<LitExtra>& cache1 = implCache[lit.toInt()].lits;
    assert(solver->watches.size() > (lit.toInt()));
    watch_subarray_const ws1 = solver->watches[lit];
    const vector<LitExtra>& cache2 = implCache[(~lit).toInt()].lits;
    watch_subarray_const ws2 = solver->watches[~lit];

    //Fill 'seen' and 'val' from cache
    for (vector<LitExtra>::const_iterator
        it = cache1.begin(), end = cache1.end()
        ; it != end
        ; ++it
    ) {
        const uint32_t var2 = it->getLit().var();

        //A variable that has been really eliminated, skip
        if (solver->varData[var2].removed != Removed::none) {
            continue;
        }

        seen[it->getLit().var()] = 1;
        val[it->getLit().var()] = it->getLit().sign();
    }

    //Fill 'seen' and 'val' from watch
    for (const Watched *it = ws1.begin(), *end = ws1.end()
        ; it != end
        ; ++it
    ) {
        if (!it->isBin())
            continue;

        const Lit otherLit = it->lit2();

        if (!seen[otherLit.var()]) {
            seen[otherLit.var()] = 1;
            val[otherLit.var()] = otherLit.sign();
        } else if (val[otherLit.var()] != otherLit.sign()) {
            //(a->b, a->-b) -> so 'a'
            delayedClausesToAddNorm.push_back(lit);
        }
    }
    //Okay, filled

    //Try to see if we propagate the same or opposite from the other end
    //Using cache
    for (vector<LitExtra>::const_iterator
        it = cache2.begin(), end = cache2.end()
        ; it != end
        ; ++it
    ) {
        assert(it->getLit().var() != var);
        const uint32_t var2 = it->getLit().var();

        //Only if the other one also contained it
        if (!seen[var2])
            continue;

        //If var has been removed, skip
        if (solver->varData[var2].removed != Removed::none) {
            continue;
        }

        handleNewData(val, var, it->getLit());
    }

    //Try to see if we propagate the same or opposite from the other end
    //Using binary clauses
    for (const Watched *it = ws2.begin(), *end = ws2.end(); it != end; ++it) {
        if (!it->isBin())
            continue;

        assert(it->lit2().var() != var);
        const uint32_t var2 = it->lit2().var();
        assert(var2 < solver->nVars());

        //Only if the other one also contained it
        if (!seen[var2])
            continue;

        handleNewData(val, var, it->lit2());
    }

    //Clear 'seen' and 'val'
    for (vector<LitExtra>::const_iterator it = cache1.begin(), end = cache1.end(); it != end; ++it) {
        seen[it->getLit().var()] = false;
        val[it->getLit().var()] = false;
    }

    for (const Watched *it = ws1.begin(), *end = ws1.end(); it != end; ++it) {
        if (!it->isBin())
            continue;

        seen[it->lit2().var()] = false;
        val[it->lit2().var()] = false;
    }
}

bool TransCache::merge(
    const vector<LitExtra>& otherLits //Lits to add
    , const Lit extraLit //Add this, too to the list of lits
    , const bool red //The step was a redundant-dependent step?
    , const uint32_t leaveOut //Leave this literal out
    , vector<uint16_t>& seen
) {
    //Mark every literal that is to be added in 'seen'
    for (size_t i = 0, size = otherLits.size(); i < size; i++) {
        const Lit lit = otherLits[i].getLit();
        const bool onlyIrred = otherLits[i].getOnlyIrredBin();

        seen[lit.toInt()] = 1 + (int)onlyIrred;
    }

    bool taut = mergeHelper(extraLit, red, seen);

    //Whatever rests needs to be added
    for (size_t i = 0 ,size = otherLits.size(); i < size; i++) {
        const Lit lit = otherLits[i].getLit();
        if (seen[lit.toInt()]) {
            if (lit.var() != leaveOut)
                lits.push_back(LitExtra(lit, !red && otherLits[i].getOnlyIrredBin()));
            seen[lit.toInt()] = 0;
        }
    }

    //Handle extra lit
    if (extraLit != lit_Undef && seen[extraLit.toInt()]) {
        if (extraLit.var() != leaveOut)
            lits.push_back(LitExtra(extraLit, !red));
        seen[extraLit.toInt()] = 0;
    }

    return taut;
}

bool TransCache::merge(
    const vector<Lit>& otherLits //Lits to add
    , const Lit extraLit //Add this, too to the list of lits
    , const bool red //The step was a redundant-dependent step?
    , const uint32_t leaveOut //Leave this literal out
    , vector<uint16_t>& seen
) {
    //Mark every literal that is to be added in 'seen'
    for (size_t i = 0, size = otherLits.size(); i < size; i++) {
        const Lit lit = otherLits[i];
        seen[lit.toInt()] = 1;
    }

    bool taut = mergeHelper(extraLit, red, seen);

    //Whatever rests needs to be added
    for (size_t i = 0 ,size = otherLits.size(); i < size; i++) {
        const Lit lit = otherLits[i];
        if (seen[lit.toInt()]) {
            if (lit.var() != leaveOut)
                lits.push_back(LitExtra(lit, false));
            seen[lit.toInt()] = 0;
        }
    }

    //Handle extra lit
    if (extraLit != lit_Undef && seen[extraLit.toInt()]) {
        if (extraLit.var() != leaveOut)
            lits.push_back(LitExtra(extraLit, !red));
        seen[extraLit.toInt()] = 0;
    }

    return taut;
}

bool TransCache::mergeHelper(
    const Lit extraLit //Add this, too to the list of lits
    , const bool red //The step was a redundant-dependent step?
    , vector<uint16_t>& seen
) {
    bool taut = false;

    //Handle extra lit
    if (extraLit != lit_Undef)
        seen[extraLit.toInt()] = 1 + (int)!red;

    //Everything that's already in the cache, set seen[] to zero
    //Also, if seen[] is 2, but it's marked redundant in the cache
    //mark it as irred
    for (size_t i = 0, size = lits.size(); i < size; i++) {
        if (!red
            && !lits[i].getOnlyIrredBin()
            && seen[lits[i].getLit().toInt()] == 2
        ) {
            lits[i].setOnlyIrredBin();
        }

        seen[lits[i].getLit().toInt()] = 0;

        //Both L and ~L are in, the ancestor is a tautology
        if (seen[(~(lits[i].getLit())).toInt()]) {
            taut = true;
        }
    }

    return taut;
}

//Make all literals as if propagated only by redundant
void TransCache::makeAllRed()
{
    for(size_t i = 0; i < lits.size(); i++) {
        lits[i] = LitExtra(lits[i].getLit(), false);
    }

}

void TransCache::updateVars(
    const std::vector< uint32_t >& outerToInter
    , const size_t newMaxVars
) {
    for(size_t i = 0; i < lits.size(); i++) {
        lits[i] = LitExtra(getUpdatedLit(lits[i].getLit(), outerToInter), lits[i].getOnlyIrredBin());
        assert(lits[i].getLit().var() < newMaxVars);
    }

}

void ImplCache::updateVars(
    vector<uint16_t>& seen
    , const std::vector< uint32_t >& outerToInter
    , const std::vector< uint32_t >& interToOuter2
    , const size_t newMaxVar
) {
    updateBySwap(implCache, seen, interToOuter2);
    for(size_t i = 0; i < implCache.size(); i++) {
        implCache[i].updateVars(outerToInter, newMaxVar);
    }
}

ImplCache::TryBothStats& ImplCache::TryBothStats::operator+=(const TryBothStats& other)
{
    numCalls += other.numCalls;
    cpu_time += other.cpu_time;
    zeroDepthAssigns += other.zeroDepthAssigns;
    varReplaced += other.varReplaced;
    bProp += other.bProp;
    bXProp += other.bXProp;

    return *this;
}

void ImplCache::TryBothStats::print_short(Solver* solver) const
{
    cout
    << "c [bcache] "
    //<< " set: " << bProp
    << " 0-depth ass: " << zeroDepthAssigns
    << " BXprop: " << bXProp
    << solver->conf.print_times(cpu_time)
    << endl;
}


#endif //TRANSCACHE_H_

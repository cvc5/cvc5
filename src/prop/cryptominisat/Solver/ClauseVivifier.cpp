/**************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
*****************************************************************************/

#include "ClauseVivifier.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include <iomanip>

//#define ASSYM_DEBUG

using namespace CMSat;

ClauseVivifier::ClauseVivifier(Solver& _solver) :
    lastTimeWentUntil(0)
    , numCalls(0)
    , solver(_solver)
{}


/**
@brief Performs clause vivification (by Hamadi et al.)

This is the only thing that does not fit under the aegis of tryBoth(), since
it is not part of failed literal probing, really. However, it is here because
it seems to be a function that fits into the idology of failed literal probing.
Maybe I am off-course and it should be in another class, or a class of its own.
*/
bool ClauseVivifier::vivifyClauses()
{
    assert(solver.ok);
    #ifdef VERBOSE_DEBUG
    std::cout << "c clauseVivifier started" << std::endl;
    //solver.printAllClauses();
    #endif //VERBOSE_DEBUG


    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    numCalls++;

    if (solver.ok) {
        if (!vivifyClauses2(solver.clauses)) return false;
        if (!vivifyClauses2(solver.learnts)) return false;
    }

    bool failed;
    uint32_t effective = 0;
    uint32_t effectiveLit = 0;
    double myTime = cpuTime();
    uint64_t maxNumProps = 20*1000*1000;
    if (solver.clauses_literals + solver.learnts_literals < 500000)
        maxNumProps *=2;
    uint64_t extraDiff = 0;
    uint64_t oldProps = solver.propagations;
    bool needToFinish = false;
    uint32_t checkedClauses = 0;
    uint32_t potentialClauses = solver.clauses.size();
    if (lastTimeWentUntil + 500 > solver.clauses.size())
        lastTimeWentUntil = 0;
    uint32_t thisTimeWentUntil = 0;
    vec<Lit> lits;
    vec<Lit> unused;

    if (solver.clauses.size() < 1000000) {
        //if too many clauses, random order will do perfectly well
        std::sort(solver.clauses.getData(), solver.clauses.getDataEnd(), sortBySize());
    }

    uint32_t queueByBy = 2;
    if (numCalls > 8
        && (solver.clauses_literals + solver.learnts_literals < 4000000)
        && (solver.clauses.size() < 50000))
        queueByBy = 1;

    Clause **i, **j;
    i = j = solver.clauses.getData();
    for (Clause **end = solver.clauses.getDataEnd(); i != end; i++) {
        if (needToFinish || lastTimeWentUntil > 0) {
            if (!needToFinish) {
                lastTimeWentUntil--;
                thisTimeWentUntil++;
            }
            *j++ = *i;
            continue;
        }

        //if done enough, stop doing it
        if (solver.propagations-oldProps + extraDiff > maxNumProps) {
            //std::cout << "Need to finish -- ran out of prop" << std::endl;
            needToFinish = true;
        }

        //if bad performance, stop doing it
        /*if ((i-solver.clauses.getData() > 5000 && effectiveLit < 300)) {
            std::cout << "Need to finish -- not effective" << std::endl;
            needToFinish = true;
        }*/

        Clause& c = **i;
        extraDiff += c.size();
        checkedClauses++;
        thisTimeWentUntil++;

        assert(c.size() > 2);
        assert(!c.learnt());

        unused.clear();
        lits.clear();
        lits.growTo(c.size());
        memcpy(lits.getData(), c.getData(), c.size() * sizeof(Lit));

        failed = false;
        uint32_t done = 0;
        solver.newDecisionLevel();
        for (; done < lits.size();) {
            uint32_t i2 = 0;
            for (; (i2 < queueByBy) && ((done+i2) < lits.size()); i2++) {
                lbool val = solver.value(lits[done+i2]);
                if (val == l_Undef) {
                    solver.uncheckedEnqueueLight(~lits[done+i2]);
                } else if (val == l_False) {
                    unused.push(lits[done+i2]);
                }
            }
            done += i2;
            failed = (!solver.propagate<false>(false).isNULL());
            if (numCalls > 3 && failed) break;
        }
        solver.cancelUntilLight();
        assert(solver.ok);

        if (unused.size() > 0 || (failed && done < lits.size())) {
            effective++;
            uint32_t origSize = lits.size();
            #ifdef ASSYM_DEBUG
            std::cout << "Assym branch effective." << std::endl;
            std::cout << "-- Orig clause:"; c.plainPrint();
            #endif
            solver.detachClause(c);

            lits.shrink(lits.size() - done);
            for (uint32_t i2 = 0; i2 < unused.size(); i2++) {
                remove(lits, unused[i2]);
            }

            Clause *c2 = solver.addClauseInt(lits);
            #ifdef ASSYM_DEBUG
            std::cout << "-- Origsize:" << origSize << " newSize:" << (c2 == NULL ? 0 : c2->size()) << " toRemove:" << c.size() - done << " unused.size():" << unused.size() << std::endl;
            #endif
            extraDiff += 20;
            //TODO cheating here: we don't detect a NULL return that is in fact a 2-long clause
            effectiveLit += origSize - (c2 == NULL ? 0 : c2->size());
            solver.clauseAllocator.clauseFree(&c);

            if (c2 != NULL) {
                #ifdef ASSYM_DEBUG
                std::cout << "-- New clause:"; c2->plainPrint();
                #endif
                *j++ = c2;
            }

            if (!solver.ok) needToFinish = true;
        } else {
            *j++ = *i;
        }
    }
    solver.clauses.shrink(i-j);

    lastTimeWentUntil = thisTimeWentUntil;

    if (solver.conf.verbosity  >= 1) {
        std::cout << "c asymm "
        << " cl-useful: " << effective << "/" << checkedClauses << "/" << potentialClauses
        << " lits-rem:" << effectiveLit
        << " time: " << cpuTime() - myTime
        << std::endl;
    }

    return solver.ok;
}


bool ClauseVivifier::vivifyClauses2(vec<Clause*>& clauses)
{
    assert(solver.ok);

    vec<char> seen;
    seen.growTo(solver.nVars()*2, 0);
    vec<char> seen_subs;
    seen_subs.growTo(solver.nVars()*2, 0);

    uint32_t litsRem = 0;
    uint32_t clShrinked = 0;
    uint64_t countTime = 0;
    uint64_t maxCountTime = 800*1000*1000;
    maxCountTime *= 6;
    if (solver.clauses_literals + solver.learnts_literals < 500000)
        maxCountTime *= 2;
    uint32_t clTried = 0;
    vec<Lit> lits;
    bool needToFinish = false;
    double myTime = cpuTime();
    uint32_t subsumed_tri_num = 0;
    uint32_t subsumed_bin_num = 0;

    Clause** i = clauses.getData();
    Clause** j = i;
    for (Clause** end = clauses.getDataEnd(); i != end; i++) {
        if (needToFinish) {
            *j++ = *i;
            continue;
        }
        if (countTime > maxCountTime)
            needToFinish = true;

        Clause& cl = **i;
        countTime += cl.size()*2;
        clTried++;

        bool subsumed = false;
        const bool learnt = cl.learnt();
        for (uint32_t i2 = 0; i2 < cl.size(); i2++) {
            seen[cl[i2].toInt()] = 1; //for strengthening
            seen_subs[cl[i2].toInt()] = 1; //for subsumption
        }

        for (const Lit *l = cl.getData(), *end = cl.getDataEnd(); l != end; l++) {
            const Lit *l_other = l;
            l_other++;
            if (l_other != end)
                __builtin_prefetch(solver.watches[(~*l_other).toInt()].getData());

            const vec<Watched>& ws = solver.watches[(~*l).toInt()];
            countTime += ws.size()*2;
            for(vec<Watched>::const_iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
                //Handle tri clause
                if (it->isTriClause() && cl.size() > 3)
                {
                    if (learnt //we cannot decide if TRI is learnt or not
                        && seen_subs[it->getOtherLit().toInt()]
                        && seen_subs[it->getOtherLit2().toInt()]
                    ) {
                        subsumed_tri_num++;
                        subsumed = true;
                    }

                    if (seen[l->toInt()]) { //we may have removed it already
                        //one way
                        if (seen[(it->getOtherLit2()).toInt()])
                            seen[(~it->getOtherLit()).toInt()] = 0;

                        //other way
                        if (seen[(it->getOtherLit()).toInt()])
                            seen[(~it->getOtherLit2()).toInt()] = 0;
                    }
                }

                //Handle Binary clause
                if (it->isBinary()) {
                    if (seen_subs[it->getOtherLit().toInt()])
                    {
                        if (!learnt && it->getLearnt())
                            makeNonLearntBin(*l, it->getOtherLit(), it->getLearnt());
                        subsumed_bin_num++;
                        subsumed = true;
                    }

                    if (seen[l->toInt()]) //we may have removed it already
                        seen[(~it->getOtherLit()).toInt()] = 0;

                }
            }

            if (seen[l->toInt()] == 0)
                continue;

            countTime += solver.transOTFCache[l->toInt()].lits.size();
            for (vector<Lit>::const_iterator it2 = solver.transOTFCache[l->toInt()].lits.begin()
                , end2 = solver.transOTFCache[l->toInt()].lits.end(); it2 != end2; it2++) {
                seen[(~(*it2)).toInt()] = 0;
            }
        }

        lits.clear();
        for (const Lit *it2 = cl.getData(), *end2 = cl.getDataEnd(); it2 != end2; it2++) {
            if (seen[it2->toInt()]) lits.push(*it2);
            else litsRem++;
            seen[it2->toInt()] = 0;
            seen_subs[it2->toInt()] = 0;
        }

        if (subsumed) {
            solver.removeClause(cl);
        } else if (lits.size() < cl.size()) {
            solver.detachClause(cl);
            clShrinked++;
            Clause* c2 = solver.addClauseInt(lits, cl.learnt(), cl.getGlue(), cl.getMiniSatAct());
            solver.clauseAllocator.clauseFree(&cl);

            if (c2 != NULL) *j++ = c2;
            if (!solver.ok) needToFinish = true;
        } else {
            *j++ = *i;
        }
    }

    clauses.shrink(i-j);

    if (solver.conf.verbosity >= 1) {
        std::cout << "c vivif2 -- "
        << " cl tried " << std::setw(8) << clTried
        << " cl rem " << std::setw(8) << (subsumed_bin_num + subsumed_tri_num)
        << " cl shrink " << std::setw(8) << clShrinked
        << " lits rem " << std::setw(10) << litsRem
        << " time: " << cpuTime() - myTime
        << std::endl;
    }

    return solver.ok;
}

void ClauseVivifier::makeNonLearntBin(const Lit lit1, const Lit lit2, const bool learnt)
{
    assert(learnt == true);
    findWatchedOfBin(solver.watches, lit1 ,lit2, learnt).setLearnt(false);
    findWatchedOfBin(solver.watches, lit2 ,lit1, learnt).setLearnt(false);
    solver.learnts_literals -= 2;
    solver.clauses_literals += 2;
}

/***********************************************************************************
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
**************************************************************************************************/

#include "XorFinder.h"

#include <algorithm>
#include <utility>
#include <iostream>
#include "Solver.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"

//#define VERBOSE_DEBUG

using namespace CMSat;
using std::make_pair;

XorFinder::XorFinder(Solver& _solver, vec<Clause*>& _cls) :
    cls(_cls)
    , solver(_solver)
{
}

bool XorFinder::fullFindXors(const uint32_t minSize, const uint32_t maxSize)
{
    uint32_t sumLengths = 0;
    double time = cpuTime();
    foundXors = 0;
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    if (!solver.ok) return false;

    toRemove.clear();
    toRemove.resize(cls.size(), false);
    toLeaveInPlace.clear();
    toLeaveInPlace.resize(cls.size(), false);

    table.clear();
    table.reserve(cls.size());

    for (Clause **it = cls.getData(), **end = cls.getDataEnd(); it != end; it ++) {
        if (it+1 != end) __builtin_prefetch(*(it+1));
        Clause& c = (**it);
        assert((*it)->size() > 2);
        bool sorted = true;
        for (uint32_t i = 0, size = c.size(); i+1 < size ; i++) {
            sorted = (c[i].var() <= c[i+1].var());
            if (!sorted) break;
        }
        if (!sorted) {
            solver.detachClause(c);
            std::sort(c.getData(), c.getDataEnd());
            solver.attachClause(c);
        }
    }

    uint32_t i = 0;
    for (Clause **it = cls.getData(), **end = cls.getDataEnd(); it != end; it++, i++) {
        const uint32_t size = (*it)->size();
        if ( size > maxSize || size < minSize) {
            toLeaveInPlace[i] = true;
            continue;
        }
        table.push_back(make_pair(*it, i));
    }
    std::sort(table.begin(), table.end(), clause_sorter_primary());

    if (!findXors(sumLengths)) goto end;
    solver.ok = (solver.propagate<true>().isNULL());

end:

    if (solver.conf.verbosity >= 1 || (solver.conf.verbosity >= 1 && foundXors > 0)) {
        printf("c Finding non-binary XORs:    %5.2f s (found: %7d, avg size: %3.1f)\n", cpuTime()-time, foundXors, (double)sumLengths/(double)foundXors);
    }

    i = 0;
    uint32_t j = 0;
    uint32_t toSkip = 0;
    for (uint32_t end = cls.size(); i != end; i++) {
        if (toLeaveInPlace[i]) {
            cls[j] = cls[i];
            j++;
            toSkip++;
            continue;
        }
        if (!toRemove[table[i-toSkip].second]) {
            cls[j] = table[i-toSkip].first;
            j++;
        }
    }
    cls.shrink(i-j);

    return solver.ok;
}


/**
@brief Finds xors in clauseTable -- datastructures must already be set up

Identifies sets of clauses of the same length and variable content, and then
tries to merge them into an XOR.
*/
bool XorFinder::findXors(uint32_t& sumLengths)
{
    #ifdef VERBOSE_DEBUG
    cout << "Finding Xors started" << endl;
    #endif

    sumLengths = 0;

    ClauseTable::iterator begin = table.begin();
    ClauseTable::iterator end = table.begin();
    vec<Lit> lits;
    bool impair;
    while (getNextXor(begin,  end, impair)) {
        const Clause& c = *(begin->first);
        lits.clear();
        for (const Lit *it = &c[0], *cend = it+c.size() ; it != cend; it++) {
            lits.push(Lit(it->var(), false));
        }

        #ifdef VERBOSE_DEBUG
        cout << "- Found clauses:" << endl;
        #endif

        for (ClauseTable::iterator it = begin; it != end; it++) {
            //This clause belongs to the xor we found?
            //(i.e. does it have the correct number of inverted literals?)
            if (impairSigns(*it->first) == impair){
                #ifdef VERBOSE_DEBUG
                it->first->plainPrint();
                #endif
                toRemove[it->second] = true;
                solver.removeClause(*it->first);
            }
        }

        assert(lits.size() > 2);
        XorClause* x = solver.addXorClauseInt(lits, impair);
        if (x != NULL) solver.xorclauses.push(x);
        if (!solver.ok) return false;

        #ifdef VERBOSE_DEBUG
        cout << "- Final xor-clause: " << x << std::endl;;
        #endif

        foundXors++;
        sumLengths += lits.size();
    }

    return solver.ok;
}

/**
@brief Moves to the next set of begin&end pointers that contain an xor

@p begin[inout] start searching here in XorFinder::table
@p end[inout] end iterator of XorFinder::table until which the xor spans
*/
bool XorFinder::getNextXor(ClauseTable::iterator& begin, ClauseTable::iterator& end, bool& impair)
{
    ClauseTable::iterator tableEnd = table.end();

    while(begin != tableEnd && end != tableEnd) {
        begin = end;
        end++;
        uint32_t size = (end == tableEnd ? 0:1);
        while(end != tableEnd && clause_vareq(begin->first, end->first)) {
            size++;
            end++;
        }
        if (size > 0 && isXor(size, begin, end, impair))
            return true;
    }

    return false;
}

/**
@brief Returns if the two clauses are equal

NOTE: assumes that the clauses are of equal lenght AND contain the same
variables (but the invertedness of the literals might differ)
*/
bool XorFinder::clauseEqual(const Clause& c1, const Clause& c2) const
{
    assert(c1.size() == c2.size());
    for (uint32_t i = 0, size = c1.size(); i < size; i++)
        if (c1[i].sign() !=  c2[i].sign()) return false;

    return true;
}

/**
@brief Returns whether the number of inverted literals in the clause is pair or impair
*/
bool XorFinder::impairSigns(const Clause& c) const
{
    uint32_t num = 0;
    for (const Lit *it = &c[0], *end = it + c.size(); it != end; it++)
        num += it->sign();

    return num % 2;
}

/**
@brief Gets as input a set of clauses of equal size and variable content, decides if there is an XOR in them

@param impair If there is an XOR, this tells if that XOR contains an impair
number of inverted literal or not
@return True, if ther is an XOR, and False if not
*/
bool XorFinder::isXor(const uint32_t size, const ClauseTable::iterator& begin, const ClauseTable::iterator& end, bool& impair)
{
    const uint32_t requiredSize = 1 << (begin->first->size()-1);

    //Note: "size" can be larger than requiredSize, since there might be
    //a mix of imparied and paired num. inverted literals, and furthermore,
    //clauses might be repeated
    if (size < requiredSize) return false;

    #ifdef DEBUG_XORFIND2
    {
        vec<Var> vars;
        Clause& c = *begin->first;
        for (uint32_t i = 0; i < c.size(); i++)
            vars.push(c[i].var());
        for (ClauseTable::iterator it = begin; it != end; it++) {
            Clause& c = *it->first;
            for (uint32_t i = 0; i < c.size(); i++)
                assert(vars[i] == c[i].var());
        }
        clause_sorter_primary sorter;

        for (ClauseTable::iterator it = begin; it != end; it++) {
            ClauseTable::iterator it2 = it;
            it2++;
            if (it2 == end) break;
            assert(!sorter(*it2, *it));
        }
    }
    #endif //DEBUG_XORFIND

    //We now sort them according to literal content
    std::sort(begin, end, clause_sorter_secondary());

    uint32_t numPair = 0;
    uint32_t numImpair = 0;
    countImpairs(begin, end, numImpair, numPair);

    //if there are two XORs with equal variable sets, but different invertedness
    //that leads to direct UNSAT result.
    if (numImpair == requiredSize && numPair == requiredSize) {
        solver.ok = false;
        impair = true;
        return true;
    }

    if (numImpair == requiredSize) {
        impair = true;
        return true;
    }

    if (numPair == requiredSize) {
        impair = false;
        return true;
    }

    return false;
}

/**
@brief Counts number of negations in the literals in clauses between begin&end, and returns the number of clauses with pair, and impair literals
*/
void XorFinder::countImpairs(const ClauseTable::iterator& begin, const ClauseTable::iterator& end, uint32_t& numImpair, uint32_t& numPair) const
{
    numImpair = 0;
    numPair = 0;

    ClauseTable::const_iterator it = begin;
    ClauseTable::const_iterator it2 = begin;
    it2++;

    bool impair = impairSigns(*it->first);
    numImpair += impair;
    numPair += !impair;

    for (; it2 != end;) {
        if (!clauseEqual(*it->first, *it2->first)) {
            bool impair = impairSigns(*it2->first);
            numImpair += impair;
            numPair += !impair;
        }
        it++;
        it2++;
    }
}

/**
@brief Converts all xor clauses to normal clauses

Sometimes it's not worth the hassle of having xor clauses and normal clauses.
This function converts xor clauses to normal clauses, and removes the normal
clauses.

\todo It currently only works for 3- and 4-long clauses. Larger clauses should
also be handled.
*/
void XorFinder::addAllXorAsNorm()
{
    uint32_t added = 0;
    XorClause **i = solver.xorclauses.getData(), **j = i;
    for (XorClause **end = solver.xorclauses.getDataEnd(); i != end; i++) {
        if ((*i)->size() > 3) {
            *j++ = *i;
            continue;
        }
        added++;
        if ((*i)->size() == 3) addXorAsNormal3(**i);
        //if ((*i)->size() == 4) addXorAsNormal4(**i);
        solver.removeClause(**i);
    }
    solver.xorclauses.shrink(i-j);
    if (solver.conf.verbosity >= 1) {
        std::cout << "c Added XOR as norm:" << added << std::endl;
    }
}

/**
@brief Utility function for addAllXorAsNorm() for converting 3-long xor clauses to normal clauses

\todo clean this up, it's ugly
*/
void XorFinder::addXorAsNormal3(XorClause& c)
{
    assert(c.size() == 3);
    Clause *tmp;
    vec<Var> vars;
    const bool inverted = c.xorEqualFalse();

    for (uint32_t i = 0; i < c.size(); i++) {
        vars.push(c[i].var());
    }

    vec<Lit> vars2;
    vars2.growTo(3);
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2.growTo(3);
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2.growTo(3);
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2.growTo(3);
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);
}

/**
@brief Utility function for addAllXorAsNorm() for converting 4-long xor clauses to normal clauses

\todo clean this up, it's ugly
*/
void XorFinder::addXorAsNormal4(XorClause& c)
{
    assert(c.size() == 4);
    Clause *tmp;
    vec<Var> vars;
    vec<Lit> vars2(c.size());
    const bool inverted = !c.xorEqualFalse();

    for (uint32_t i = 0; i < c.size(); i++) {
        vars.push(c[i].var());
    }

    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);

    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2);
    if (tmp) solver.clauses.push(tmp);
}

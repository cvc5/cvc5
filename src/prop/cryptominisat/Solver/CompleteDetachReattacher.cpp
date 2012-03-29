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

#include "CompleteDetachReattacher.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"

using namespace CMSat;

CompleteDetachReatacher::CompleteDetachReatacher(Solver& _solver) :
    solver(_solver)
{
}

/**
@brief Completely detach all non-binary clauses
*/
void CompleteDetachReatacher::detachNonBinsNonTris(const bool removeTri)
{
    uint32_t oldNumBins = solver.numBins;
    ClausesStay stay;

    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++) {
        stay += clearWatchNotBinNotTri(*it, removeTri);
    }

    solver.learnts_literals = stay.learntBins;
    solver.clauses_literals = stay.nonLearntBins;
    solver.numBins = (stay.learntBins + stay.nonLearntBins)/2;
    release_assert(solver.numBins == oldNumBins);
}

/**
@brief Helper function for detachPointerUsingClauses()
*/
const CompleteDetachReatacher::ClausesStay CompleteDetachReatacher::clearWatchNotBinNotTri(vec<Watched>& ws, const bool removeTri)
{
    ClausesStay stay;

    vec<Watched>::iterator i = ws.getData();
    vec<Watched>::iterator j = i;
    for (vec<Watched>::iterator end = ws.getDataEnd(); i != end; i++) {
        if (i->isBinary()) {
            if (i->getLearnt()) stay.learntBins++;
            else stay.nonLearntBins++;
            *j++ = *i;
        } else if (!removeTri && i->isTriClause()) {
            stay.tris++;
            *j++ = *i;
        }
    }
    ws.shrink_(i-j);

    return stay;
}

/**
@brief Completely attach all clauses
*/
bool CompleteDetachReatacher::reattachNonBins()
{
    assert(solver.ok);

    cleanAndAttachClauses(solver.clauses);
    cleanAndAttachClauses(solver.learnts);
    cleanAndAttachClauses(solver.xorclauses);
    solver.clauseCleaner->removeSatisfiedBins();

    if (solver.ok) solver.ok = (solver.propagate<false>().isNULL());

    return solver.ok;
}

/**
@brief Cleans clauses from failed literals/removes satisfied clauses from cs

May change solver.ok to FALSE (!)
*/
inline void CompleteDetachReatacher::cleanAndAttachClauses(vec<Clause*>& cs)
{
    Clause **i = cs.getData();
    Clause **j = i;
    PolaritySorter sorter(solver.polarity);
    for (Clause **end = cs.getDataEnd(); i != end; i++) {
        std::sort((*i)->getData(), (*i)->getDataEnd(), sorter);
        if (cleanClause(*i)) {
            solver.attachClause(**i);
            *j++ = *i;
        } else {
            solver.clauseAllocator.clauseFree(*i);
        }
    }
    cs.shrink(i-j);
}

/**
@brief Cleans clauses from failed literals/removes satisfied clauses from cs
*/
inline void CompleteDetachReatacher::cleanAndAttachClauses(vec<XorClause*>& cs)
{
    XorClause **i = cs.getData();
    XorClause **j = i;
    for (XorClause **end = cs.getDataEnd(); i != end; i++) {
        if (cleanClause(**i)) {
            solver.attachClause(**i);
            *j++ = *i;
        } else {
            solver.clauseAllocator.clauseFree(*i);
        }
    }
    cs.shrink(i-j);
}

/**
@brief Not only cleans a clause from false literals, but if clause is satisfied, it reports it
*/
inline bool CompleteDetachReatacher::cleanClause(Clause*& cl)
{
    Clause& ps = *cl;
    assert(ps.size() > 2);

    Lit *i = ps.getData();
    Lit *j = i;
    for (Lit *end = ps.getDataEnd(); i != end; i++) {
        if (solver.value(*i) == l_True) return false;
        if (solver.value(*i) == l_Undef) {
            *j++ = *i;
        }
    }
    ps.shrink(i-j);

    switch (ps.size()) {
        case 0:
            solver.ok = false;
            return false;
        case 1:
            solver.uncheckedEnqueue(ps[0]);
            return false;

        case 2: {
            solver.attachBinClause(ps[0], ps[1], ps.learnt());
            return false;
        }

        default:;
    }

    return true;
}

/**
@brief Not only cleans a clause from false literals, but if clause is satisfied, it reports it
*/
inline bool CompleteDetachReatacher::cleanClause(XorClause& ps)
{
    Lit *i = ps.getData(), *j = i;
    for (Lit *end = ps.getDataEnd(); i != end; i++) {
        if (solver.assigns[i->var()] == l_True) ps.invert(true);
        if (solver.assigns[i->var()] == l_Undef) {
            *j++ = *i;
        }
    }
    ps.shrink(i-j);

    switch (ps.size()) {
        case 0:
            if (ps.xorEqualFalse() == false) solver.ok = false;
            return false;
        case 1:
            solver.uncheckedEnqueue(Lit(ps[0].var(), ps.xorEqualFalse()));
            return false;

        case 2: {
            ps[0] = ps[0].unsign();
            ps[1] = ps[1].unsign();
            solver.varReplacer->replace(ps, ps.xorEqualFalse());
            return false;
        }

        default:;
    }

    return true;
}

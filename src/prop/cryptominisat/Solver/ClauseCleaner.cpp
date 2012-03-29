/***************************************************************************
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
****************************************************************************/

#include "ClauseCleaner.h"
#include "VarReplacer.h"
#include "DataSync.h"

//#define DEBUG_CLEAN
//#define VERBOSE_DEBUG

using namespace CMSat;

ClauseCleaner::ClauseCleaner(Solver& _solver) :
    solver(_solver)
{
    for (uint32_t i = 0; i < 6; i++) {
        lastNumUnitarySat[i] = solver.get_unitary_learnts_num();
        lastNumUnitaryClean[i] = solver.get_unitary_learnts_num();
    }
}

bool ClauseCleaner::satisfied(const Watched& watched, Lit lit)
{
    assert(watched.isBinary());
    if (solver.value(lit) == l_True) return true;
    if (solver.value(watched.getOtherLit()) == l_True) return true;
    return false;
}

void ClauseCleaner::removeSatisfiedBins(const uint32_t limit)
{
    #ifdef DEBUG_CLEAN
    assert(solver.decisionLevel() == 0);
    #endif

    if (lastNumUnitarySat[binaryClauses] + limit >= solver.get_unitary_learnts_num())
        return;

    uint32_t numRemovedHalfNonLearnt = 0;
    uint32_t numRemovedHalfLearnt = 0;
    uint32_t wsLit = 0;
    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++, wsLit++) {
        Lit lit = ~Lit::toLit(wsLit);
        vec<Watched>& ws = *it;

        vec<Watched>::iterator i = ws.getData();
        vec<Watched>::iterator j = i;
        for (vec<Watched>::iterator end2 = ws.getDataEnd(); i != end2; i++) {
            if (i->isBinary() && satisfied(*i, lit)) {
                if (i->getLearnt()) numRemovedHalfLearnt++;
                else {
                    numRemovedHalfNonLearnt++;
                }
            } else {
                *j++ = *i;
            }
        }
        ws.shrink_(i - j);
    }

    //std::cout << "removedHalfLeart: " << numRemovedHalfLearnt << std::endl;
    //std::cout << "removedHalfNonLeart: " << numRemovedHalfNonLearnt << std::endl;
    assert(numRemovedHalfLearnt % 2 == 0);
    assert(numRemovedHalfNonLearnt % 2 == 0);
    solver.clauses_literals -= numRemovedHalfNonLearnt;
    solver.learnts_literals -= numRemovedHalfLearnt;
    solver.numBins -= (numRemovedHalfLearnt + numRemovedHalfNonLearnt)/2;

    lastNumUnitarySat[binaryClauses] = solver.get_unitary_learnts_num();
}

void ClauseCleaner::cleanClauses(vec<Clause*>& cs, ClauseSetType type, const uint32_t limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());

    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;

    #ifdef VERBOSE_DEBUG
    std::cout << "Cleaning " << (type==binaryClauses ? "binaryClauses" : "normal clauses" ) << std::endl;
    #endif //VERBOSE_DEBUG

    Clause **s, **ss, **end;
    for (s = ss = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end) __builtin_prefetch(*(s+1));

        if (cleanClause(*s)) {
            solver.clauseAllocator.clauseFree(*s);
        } else {
            *ss++ = *s;
        }
    }
    cs.shrink(s-ss);

    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();

    #ifdef VERBOSE_DEBUG
    cout << "cleanClauses(Clause) useful ?? Removed: " << s-ss << endl;
    #endif
}

inline bool ClauseCleaner::cleanClause(Clause*& cc)
{
    Clause& c = *cc;

    Lit origLit1 = c[0];
    Lit origLit2 = c[1];
    uint32_t origSize = c.size();
    Lit origLit3 = (origSize == 3) ? c[2] : lit_Undef;

    Lit *i, *j, *end;
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }

        if (val == l_True) {
            solver.detachModifiedClause(origLit1, origLit2, origLit3, origSize, &c);
            return true;
        }
    }
    c.shrink(i-j);

    assert(c.size() != 1);
    if (i != j) {
        if (c.size() == 2) {
            solver.detachModifiedClause(origLit1, origLit2, origLit3, origSize, &c);
            solver.attachBinClause(c[0], c[1], c.learnt());
            solver.numNewBin++;
            solver.dataSync->signalNewBinClause(c);
            return true;
        } else if (c.size() == 3) {
            solver.detachModifiedClause(origLit1, origLit2, origLit3, origSize, &c);
            solver.attachClause(c);
        } else {
            if (c.learnt())
                solver.learnts_literals -= i-j;
            else
                solver.clauses_literals -= i-j;
        }
    }

    return false;
}

void ClauseCleaner::cleanClauses(vec<XorClause*>& cs, ClauseSetType type, const uint32_t limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());

    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;

    XorClause **s, **ss, **end;
    for (s = ss = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end)
            __builtin_prefetch(*(s+1), 1, 0);

        #ifdef DEBUG_ATTACH_FULL
        XorClause& c = **s;
        assert(solver.xorClauseIsAttached(c));
        if (solver.assigns[c[0].var()]!=l_Undef || solver.assigns[c[1].var()]!=l_Undef) {
            satisfied(**s);
        }
        #endif //DEBUG_ATTACH

        if (cleanClause(**s)) {
            //solver.clauseAllocator.clauseFree(*s);
            solver.freeLater.push(*s);
            (*s)->setRemoved();
        } else {
            #ifdef DEBUG_ATTACH_FULL
            assert(solver.xorClauseIsAttached(c));
            #endif //DEBUG_ATTACH
            *ss++ = *s;
        }
    }
    cs.shrink(s-ss);

    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();

    #ifdef VERBOSE_DEBUG
    cout << "cleanClauses(XorClause) useful: ?? Removed: " << s-ss << endl;
    #endif
}

inline bool ClauseCleaner::cleanClause(XorClause& c)
{
    Lit *i, *j, *end;
    Var origVar1 = c[0].var();
    Var origVar2 = c[1].var();
    uint32_t origSize = c.size();
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        const lbool& val = solver.assigns[i->var()];
        if (val.isUndef()) {
            *j = *i;
            j++;
        } else c.invert(val.getBool());
    }
    c.shrink(i-j);

    assert(c.size() != 1);
    switch (c.size()) {
        case 0: {
            solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
            return true;
        }
        case 2: {
            c[0] = c[0].unsign();
            c[1] = c[1].unsign();
            solver.varReplacer->replace(c, c.xorEqualFalse());
            solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
            return true;
        }
        default: {
            if (i-j > 0) {
                solver.clauses_literals -= i-j;
            }
            return false;
        }
    }

    assert(false);
    return false;
}

bool ClauseCleaner::satisfied(const Clause& c) const
{
    for (uint32_t i = 0; i != c.size(); i++)
        if (solver.value(c[i]) == l_True)
            return true;
        return false;
}

bool ClauseCleaner::satisfied(const XorClause& c) const
{
    bool final = c.xorEqualFalse();
    for (uint32_t k = 0; k != c.size(); k++ ) {
        const lbool& val = solver.assigns[c[k].var()];
        if (val.isUndef()) return false;
        final ^= val.getBool();
    }
    return final;
}

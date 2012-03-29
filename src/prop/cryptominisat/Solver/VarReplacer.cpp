/*****************************************************************************
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
******************************************************************************/

#include "VarReplacer.h"
#include <iostream>
#include <iomanip>
#include <set>

#include "ClauseCleaner.h"
#include "time_mem.h"
#include "DataSync.h"

//#define VERBOSE_DEBUG
//#define DEBUG_REPLACER
//#define REPLACE_STATISTICS
//#define DEBUG_BIN_REPLACER

using namespace CMSat;

VarReplacer::VarReplacer(Solver& _solver) :
    replacedLits(0)
    , replacedVars(0)
    , lastReplacedVars(0)
    , solver(_solver)
{
}

VarReplacer::~VarReplacer()
{
}

/**
@brief Replaces variables, clears internal clauses, and reports stats

When replacing, it is imperative not to make variables decision variables
which have been removed by other methods:
\li variable removal at the xor-sphere
\li disconnected component finding and solving
\li variable elimination

NOTE: If any new such algoirhtms are added, this part MUST be updated such
that problems don't creep up
*/
bool VarReplacer::performReplaceInternal()
{
    #ifdef VERBOSE_DEBUG
    cout << "PerformReplacInternal started." << endl;
    //solver.printAllClauses();
    #endif
    double time = cpuTime();

    #ifdef REPLACE_STATISTICS
    uint32_t numRedir = 0;
    for (uint32_t i = 0; i < table.size(); i++) {
        if (table[i].var() != i)
            numRedir++;
    }
    std::cout << "Number of trees:" << reverseTable.size() << std::endl;
    std::cout << "Number of redirected nodes:" << numRedir << std::endl;
    #endif //REPLACE_STATISTICS

    solver.clauseCleaner->removeAndCleanAll(true);
    if (!solver.ok) return false;
    solver.testAllClauseAttach();
    std::fill(cannot_eliminate.getData(), cannot_eliminate.getDataEnd(), false);

    #ifdef VERBOSE_DEBUG
    {
        uint32_t i = 0;
        for (vector<Lit>::const_iterator it = table.begin(); it != table.end(); it++, i++) {
            if (it->var() == i) continue;
            cout << "Replacing var " << i+1 << " with Lit " << *it << endl;
        }
    }
    #endif

    Var var = 0;
    const vec<char>& removedVars = solver.xorSubsumer->getVarElimed();
    const vec<char>& removedVars3 = solver.subsumer->getVarElimed();
    for (vector<Lit>::const_iterator it = table.begin(); it != table.end(); it++, var++) {
        if (it->var() == var
            || removedVars[it->var()]
            || removedVars3[it->var()]
        ) continue;
        #ifdef VERBOSE_DEBUG
        cout << "Setting var " << var+1 << " to a non-decision var" << endl;
        #endif
        bool wasDecisionVar = solver.decision_var[var];
        solver.setDecisionVar(var, false);
        //cannot_eliminate[var] = true;
        solver.setDecisionVar(it->var(), true);
        assert(!removedVars[var]);
        assert(!removedVars3[var]);

        uint32_t& activity1 = solver.activity[var];
        uint32_t& activity2 = solver.activity[it->var()];
        if (wasDecisionVar && activity1 > activity2) {
            activity2 = activity1;
            solver.order_heap.update(it->var());
            solver.polarity[it->var()] = ((bool)solver.polarity[var]) ^ it->sign();
        }

        activity1 = 0.0;
        solver.order_heap.update(var);
    }
    assert(solver.order_heap.heapProperty());

    uint32_t thisTimeReplaced = replacedVars -lastReplacedVars;
    lastReplacedVars = replacedVars;

    solver.testAllClauseAttach();
    assert(solver.qhead == solver.trail.size());

    solver.countNumBinClauses(true, false);
    solver.countNumBinClauses(false, true);

    if (!replaceBins()) goto end;
    if (!replace_set(solver.clauses)) goto end;
    if (!replace_set(solver.learnts)) goto end;
    if (!replace_set(solver.xorclauses)) goto end;
    solver.testAllClauseAttach();

end:
    assert(solver.qhead == solver.trail.size() || !solver.ok);

    if (solver.conf.verbosity  >= 3) {
        std::cout << "c Replacing "
        << std::setw(8) << thisTimeReplaced << " vars"
        << " Replaced " <<  std::setw(8) << replacedLits<< " lits"
        << " Time: " << std::setw(8) << std::fixed << std::setprecision(2)
        << cpuTime()-time << " s "
        << std::endl;
    }

    replacedLits = 0;

    solver.order_heap.filter(Solver::VarFilter(solver));

    return solver.ok;
}

/**
@brief Replaces vars in xorclauses
*/
bool VarReplacer::replace_set(vec<XorClause*>& cs)
{
    XorClause **a = cs.getData();
    XorClause **r = a;
    for (XorClause **end = a + cs.size(); r != end; r++) {
        XorClause& c = **r;

        bool changed = false;
        Var origVar1 = c[0].var();
        Var origVar2 = c[1].var();

        for (Lit *l = &c[0], *end2 = l + c.size(); l != end2; l++) {
            Lit newlit = table[l->var()];
            if (newlit.var() != l->var()) {
                changed = true;
                *l = Lit(newlit.var(), false);
                c.invert(newlit.sign());
                replacedLits++;
            }
        }

        if (changed && handleUpdatedClause(c, origVar1, origVar2)) {
            if (!solver.ok) {
                #ifdef VERBOSE_DEBUG
                cout << "contradiction while replacing lits in xor clause" << std::endl;
                #endif
                for(;r != end; r++) solver.clauseAllocator.clauseFree(*r);
                cs.shrink(r-a);
                return false;
            }
            //solver.clauseAllocator.clauseFree(&c);
            c.setRemoved();
            solver.freeLater.push(&c);
        } else {
            #ifdef SILENT_DEBUG
            uint32_t numUndef = 0;
            for (uint32_t i = 0; i < c.size(); i++) {
                if (solver.value(c[i]) == l_Undef) numUndef++;
            }
            assert(numUndef >= 2 || numUndef == 0);
            #endif
            *a++ = *r;
        }
    }
    cs.shrink(r-a);

    return solver.ok;
}

/**
@brief Helper function for replace_set()
*/
bool VarReplacer::handleUpdatedClause(XorClause& c, const Var origVar1, const Var origVar2)
{
    uint32_t origSize = c.size();
    std::sort(c.getData(), c.getDataEnd());
    Lit p;
    uint32_t i, j;
    for (i = j = 0, p = lit_Undef; i != c.size(); i++) {
        if (c[i].var() == p.var()) {
            //added, but easily removed
            j--;
            p = lit_Undef;
            if (!solver.assigns[c[i].var()].isUndef())
                c.invert(solver.assigns[c[i].var()].getBool());
        } else if (solver.assigns[c[i].var()].isUndef()) //just add
            c[j++] = p = c[i];
        else c.invert(solver.assigns[c[i].var()].getBool()); //modify xorEqualFalse instead of adding
    }
    c.shrink(i - j);

    //Even if i==j, the clause *has* changed
    c.setChanged();

    #ifdef VERBOSE_DEBUG
    cout << "xor-clause after replacing: ";
    c.plainPrint();
    #endif

    switch (c.size()) {
    case 0:
        solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
        if (!c.xorEqualFalse()) {
            solver.ok = false;
        }
        return true;
    case 1:
        solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
        solver.uncheckedEnqueue(Lit(c[0].var(), c.xorEqualFalse()));
        solver.ok = (solver.propagate<false>().isNULL());
        return true;
    case 2: {
        solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
        c[0] = c[0].unsign() ^ c.xorEqualFalse();
        c[1] = c[1].unsign();
        addBinaryXorClause(c[0], c[1]);
        return true;
    }
    default:
        solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
        solver.attachClause(c);
        return false;
    }

    assert(false);
    return false;
}

bool VarReplacer::replaceBins()
{
    #ifdef DEBUG_BIN_REPLACER
    vec<uint32_t> removed(solver.nVars()*2, 0);
    uint32_t replacedLitsBefore = replacedLits;
    #endif

    uint32_t removedLearnt = 0;
    uint32_t removedNonLearnt = 0;
    uint32_t wsLit = 0;
    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++, wsLit++) {
        Lit lit1 = ~Lit::toLit(wsLit);
        vec<Watched>& ws = *it;

        vec<Watched>::iterator i = ws.getData();
        vec<Watched>::iterator j = i;
        for (vec<Watched>::iterator end2 = ws.getDataEnd(); i != end2; i++) {
            if (!i->isBinary()) {
                *j++ = *i;
                continue;
            }
            //std::cout << "bin: " << lit1 << " , " << i->getOtherLit() << " learnt : " <<  (i->isLearnt()) << std::endl;
            Lit thisLit1 = lit1;
            Lit lit2 = i->getOtherLit();
            assert(thisLit1.var() != lit2.var());

            if (table[lit2.var()].var() != lit2.var()) {
                lit2 = table[lit2.var()] ^ lit2.sign();
                i->setOtherLit(lit2);
                replacedLits++;
            }

            bool changedMain = false;
            if (table[thisLit1.var()].var() != thisLit1.var()) {
                thisLit1 = table[thisLit1.var()] ^ thisLit1.sign();
                replacedLits++;
                changedMain = true;
            }

            if (thisLit1 == lit2) {
                if (solver.value(lit2) == l_Undef) {
                    solver.uncheckedEnqueue(lit2);
                } else if (solver.value(lit2) == l_False) {
                    #ifdef VERBOSE_DEBUG
                    std::cout << "Contradiction during replacement of lits in binary clause" << std::endl;
                    #endif
                    solver.ok = false;
                }
                #ifdef DEBUG_BIN_REPLACER
                removed[lit1.toInt()]++;
                removed[origLit2.toInt()]++;
                #endif

                if (i->getLearnt()) removedLearnt++;
                else removedNonLearnt++;
                continue;
            }

            if (thisLit1 == ~lit2) {
                #ifdef DEBUG_BIN_REPLACER
                removed[lit1.toInt()]++;
                removed[origLit2.toInt()]++;
                #endif

                if (i->getLearnt()) removedLearnt++;
                else removedNonLearnt++;
                continue;
            }

            if (changedMain) {
                solver.watches[(~thisLit1).toInt()].push(*i);
            } else {
                *j++ = *i;
            }
        }
        ws.shrink_(i-j);
    }

    #ifdef DEBUG_BIN_REPLACER
    for (uint32_t i = 0; i < removed.size(); i++) {
        if (removed[i] % 2 != 0) {
            std::cout << "suspicious: " << Lit::toLit(i) << std::endl;
            std::cout << "num: " << removed[i] << std::endl;
        }
    }
    std::cout << "replacedLitsdiff: " << replacedLits - replacedLitsBefore << std::endl;
    std::cout << "removedLearnt: " << removedLearnt << std::endl;
    std::cout << "removedNonLearnt: " << removedNonLearnt << std::endl;
    #endif

    assert(removedLearnt % 2 == 0);
    assert(removedNonLearnt % 2 == 0);
    solver.learnts_literals -= removedLearnt;
    solver.clauses_literals -= removedNonLearnt;
    solver.numBins -= (removedLearnt + removedNonLearnt)/2;

    if (solver.ok) solver.ok = (solver.propagate<false>().isNULL());
    return solver.ok;
}

/**
@brief Replaces variables in normal clauses
*/
bool VarReplacer::replace_set(vec<Clause*>& cs)
{
    Clause **a = cs.getData();
    Clause **r = a;
    for (Clause **end = a + cs.size(); r != end; r++) {
        Clause& c = **r;
        assert(c.size() > 2);
        bool changed = false;
        Lit origLit1 = c[0];
        Lit origLit2 = c[1];
        Lit origLit3 = (c.size() == 3) ? c[2] : lit_Undef;
        for (Lit *l = c.getData(), *end2 = l + c.size();  l != end2; l++) {
            if (table[l->var()].var() != l->var()) {
                changed = true;
                *l = table[l->var()] ^ l->sign();
                replacedLits++;
            }
        }

        if (changed && handleUpdatedClause(c, origLit1, origLit2, origLit3)) {
            if (!solver.ok) {
                #ifdef VERBOSE_DEBUG
                cout << "contradiction while replacing lits in normal clause" << std::endl;
                #endif
                for(;r != end; r++) solver.clauseAllocator.clauseFree(*r);
                cs.shrink(r-a);
                return false;
            }
        } else {
            *a++ = *r;
        }
    }
    cs.shrink(r-a);

    return solver.ok;
}

/**
@brief Helper function for replace_set()
*/
bool VarReplacer::handleUpdatedClause(Clause& c, const Lit origLit1, const Lit origLit2, const Lit origLit3)
{
    bool satisfied = false;
    std::sort(c.getData(), c.getData() + c.size());
    Lit p;
    uint32_t i, j;
    const uint32_t origSize = c.size();
    for (i = j = 0, p = lit_Undef; i != origSize; i++) {
        if (solver.value(c[i]) == l_True || c[i] == ~p) {
            satisfied = true;
            break;
        }
        else if (solver.value(c[i]) != l_False && c[i] != p)
            c[j++] = p = c[i];
    }
    c.shrink(i - j);
    c.setChanged();

    solver.detachModifiedClause(origLit1, origLit2, origLit3, origSize, &c);

    #ifdef VERBOSE_DEBUG
    cout << "clause after replacing: ";
    c.plainPrint();
    #endif

    if (satisfied) return true;

    switch(c.size()) {
    case 0:
        solver.ok = false;
        return true;
    case 1 :
        solver.uncheckedEnqueue(c[0]);
        solver.ok = (solver.propagate<false>().isNULL());
        return true;
    case 2:
        solver.attachBinClause(c[0], c[1], c.learnt());
        solver.numNewBin++;
        solver.dataSync->signalNewBinClause(c);
        return true;
    default:
        solver.attachClause(c);
        return false;
    }

    assert(false);
    return false;
}

/**
@brief Returns variables that have been replaced
*/
vector<Var> VarReplacer::getReplacingVars() const
{
    vector<Var> replacingVars;

    for(map<Var, vector<Var> >::const_iterator it = reverseTable.begin(), end = reverseTable.end(); it != end; it++) {
        replacingVars.push_back(it->first);
    }

    return replacingVars;
}

/**
@brief Given a partial model, it tries to extend it to variables that have been replaced

Cannot extend it fully, because it might be that a replaced d&f, but a was
later variable-eliminated. That's where extendModelImpossible() comes in
*/
void VarReplacer::extendModelPossible() const
{
    #ifdef VERBOSE_DEBUG
    std::cout << "extendModelPossible() called" << std::endl;
    #endif //VERBOSE_DEBUG
    uint32_t i = 0;
    for (vector<Lit>::const_iterator it = table.begin(); it != table.end(); it++, i++) {
        if (it->var() == i) continue;

        #ifdef VERBOSE_DEBUG
        cout << "Extending model: var "; solver.printLit(Lit(i, false));
        cout << " to "; solver.printLit(*it);
        cout << endl;
        #endif

        if (solver.assigns[it->var()] != l_Undef) {
            if (solver.assigns[i] == l_Undef) {
                bool val = (solver.assigns[it->var()] == l_False);
                solver.uncheckedEnqueue(Lit(i, val ^ it->sign()));
            } else {
                assert(solver.assigns[i].getBool() == (solver.assigns[it->var()].getBool() ^ it->sign()));
            }
        }
        solver.ok = (solver.propagate<false>().isNULL());
        assert(solver.ok);
    }
}

/**
@brief Used when a variable was eliminated, but it replaced some other variables

This function will add to solver2 clauses that represent the relationship of
the variables to their replaced cousins. Then, calling solver2.solve() should
take care of everything
*/
void VarReplacer::extendModelImpossible(Solver& solver2) const
{

    #ifdef VERBOSE_DEBUG
    std::cout << "extendModelImpossible() called" << std::endl;
    #endif //VERBOSE_DEBUG

    vec<Lit> tmpClause;
    uint32_t i = 0;
    for (vector<Lit>::const_iterator it = table.begin(); it != table.end(); it++, i++) {
        if (it->var() == i) continue;
        if (solver.assigns[it->var()] == l_Undef) {
            assert(solver.assigns[it->var()] == l_Undef);
            assert(solver.assigns[i] == l_Undef);

            tmpClause.clear();
            tmpClause.push(Lit(it->var(), true));
            tmpClause.push(Lit(i, it->sign()));
            solver2.addClause(tmpClause);
            assert(solver2.ok);

            tmpClause.clear();
            tmpClause.push(Lit(it->var(), false));
            tmpClause.push(Lit(i, it->sign()^true));
            solver2.addClause(tmpClause);
            assert(solver2.ok);
        }
    }
}

/**
@brief Replaces two two vars in "ps" with one another. xorEqualFalse defines anti/equivalence

It can be tricky to do this. For example, if:

\li a replaces: b, c
\li f replaces: f, h
\li we just realised that c = h
This is the most difficult case, but there are other cases, e.g. if we already
know that c=h, in which case we don't do anything

@p ps must contain 2 variables(!), i.e literals with no sign
@p xorEqualFalse if True, the two variables are equivalent. Otherwise, they are antivalent
@p group of clause they have been inspired from. Sometimes makes no sense...
*/
template<class T>
bool VarReplacer::replace(T& ps, const bool xorEqualFalse, const bool addBinAsLearnt, const bool addToWatchLists)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "replace() called with var " << ps[0].var()+1 << " and var " << ps[1].var()+1 << " with xorEqualFalse " << xorEqualFalse << std::endl;
    #endif

    assert(solver.decisionLevel() == 0);
    assert(ps.size() == 2);
    assert(!ps[0].sign());
    assert(!ps[1].sign());
    #ifdef DEBUG_REPLACER
    assert(solver.assigns[ps[0].var()].isUndef());
    assert(solver.assigns[ps[1].var()].isUndef());

    assert(!solver.subsumer->getVarElimed()[ps[0].var()]);
    assert(!solver.xorSubsumer->getVarElimed()[ps[0].var()]);

    assert(!solver.subsumer->getVarElimed()[ps[1].var()]);
    assert(!solver.xorSubsumer->getVarElimed()[ps[1].var()]);
    #endif

    //Detect circle
    Lit lit1 = ps[0];
    lit1 = table[lit1.var()];
    Lit lit2 = ps[1];
    lit2 = table[lit2.var()] ^ !xorEqualFalse;

    //Already inside?
    if (lit1.var() == lit2.var()) {
        if (lit1.sign() != lit2.sign()) {
            solver.ok = false;
            return false;
        }
        return true;
    }

    #ifdef DEBUG_REPLACER
    assert(!solver.subsumer->getVarElimed()[lit1.var()]);
    assert(!solver.xorSubsumer->getVarElimed()[lit1.var()]);
    assert(!solver.subsumer->getVarElimed()[lit2.var()]);
    assert(!solver.xorSubsumer->getVarElimed()[lit2.var()]);
    #endif

    cannot_eliminate[lit1.var()] = true;
    cannot_eliminate[lit2.var()] = true;
    lbool val1 = solver.value(lit1);
    lbool val2 = solver.value(lit2);
    if (val1 != l_Undef && val2 != l_Undef) {
        if (val1 != val2) {
            solver.ok = false;
            return false;
        }
        return true;
    }

    if ((val1 != l_Undef && val2 == l_Undef) || (val2 != l_Undef && val1 == l_Undef)) {
        //exactly one l_Undef, exectly one l_True/l_False
        if (val1 != l_Undef) solver.uncheckedEnqueue(lit2 ^ (val1 == l_False));
        else solver.uncheckedEnqueue(lit1 ^ (val2 == l_False));

        if (solver.ok) solver.ok = (solver.propagate<false>().isNULL());
        return solver.ok;
    }

    #ifdef DEBUG_REPLACER
    assert(val1 == l_Undef && val2 == l_Undef);
    #endif //DEBUG_REPLACER

    if (addToWatchLists)
        addBinaryXorClause(lit1, lit2 ^ true, addBinAsLearnt);

    if (reverseTable.find(lit1.var()) == reverseTable.end()) {
        reverseTable[lit2.var()].push_back(lit1.var());
        table[lit1.var()] = lit2 ^ lit1.sign();
        replacedVars++;
        return true;
    }

    if (reverseTable.find(lit2.var()) == reverseTable.end()) {
        reverseTable[lit1.var()].push_back(lit2.var());
        table[lit2.var()] = lit1 ^ lit2.sign();
        replacedVars++;
        return true;
    }

    //both have children
    setAllThatPointsHereTo(lit1.var(), lit2 ^ lit1.sign()); //erases reverseTable[lit1.var()]
    replacedVars++;
    return true;
}

template bool VarReplacer::replace(vec<Lit>& ps, const bool xorEqualFalse, const bool addBinAsLearnt, const bool addToWatchLists);
template bool VarReplacer::replace(XorClause& ps, const bool xorEqualFalse, const bool addBinAsLearnt, const bool addToWatchLists);

/**
@brief Adds a binary xor to the internal/external clause set

It is added externally ONLY if we are in the middle of replacing clauses,
and a new binary xor just came up. That is a very strange and unfortunate
experience, as we cannot change the datastructures in the middle of replacement
so we add this to the binary clauses of Solver, and we recover it next time.

\todo Clean this messy internal/external thing using a better datastructure.
*/
void VarReplacer::addBinaryXorClause(Lit lit1, Lit lit2, const bool addBinAsLearnt)
{
    solver.attachBinClause(lit1, lit2, addBinAsLearnt);
    solver.dataSync->signalNewBinClause(lit1, lit2);

    lit1 ^= true;
    lit2 ^= true;
    solver.attachBinClause(lit1, lit2, addBinAsLearnt);
    solver.dataSync->signalNewBinClause(lit1, lit2);
}

/**
@brief Returns if we already know that var = lit

Also checks if var = ~lit, in which it sets solver.ok = false
*/
bool VarReplacer::alreadyIn(const Var var, const Lit lit)
{
    Lit lit2 = table[var];
    if (lit2.var() == lit.var()) {
        if (lit2.sign() != lit.sign()) {
            #ifdef VERBOSE_DEBUG
            cout << "Inverted cycle in var-replacement -> UNSAT" << endl;
            #endif
            solver.ok = false;
        }
        return true;
    }

    lit2 = table[lit.var()];
    if (lit2.var() == var) {
        if (lit2.sign() != lit.sign()) {
            #ifdef VERBOSE_DEBUG
            cout << "Inverted cycle in var-replacement -> UNSAT" << endl;
            #endif
            solver.ok = false;
        }
        return true;
    }

    return false;
}

/**
@brief Changes internal graph to set everything that pointed to var to point to lit
*/
void VarReplacer::setAllThatPointsHereTo(const Var var, const Lit lit)
{
    map<Var, vector<Var> >::iterator it = reverseTable.find(var);
    if (it != reverseTable.end()) {
        for(vector<Var>::const_iterator it2 = it->second.begin(), end = it->second.end(); it2 != end; it2++) {
            assert(table[*it2].var() == var);
            if (lit.var() != *it2) {
                table[*it2] = lit ^ table[*it2].sign();
                reverseTable[lit.var()].push_back(*it2);
            }
        }
        reverseTable.erase(it);
    }
    table[var] = lit;
    reverseTable[lit.var()].push_back(var);
}

void VarReplacer::newVar()
{
    table.push_back(Lit(table.size(), false));
    cannot_eliminate.push(false);
}

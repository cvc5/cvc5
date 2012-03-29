/*****************************************************************************
SatELite -- (C) Niklas Een, Niklas Sorensson, 2004
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Original code by SatELite authors are under an MIT licence.
Modifications for CryptoMiniSat are under GPLv3 licence.
******************************************************************************/

#include "Solver.h"
#include "Subsumer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "assert.h"
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "VarReplacer.h"
#include "XorFinder.h"
#include "CompleteDetachReattacher.h"
#include "OnlyNonLearntBins.h"
#include "UselessBinRemover.h"
#include "DataSync.h"
#include "constants.h"
#include "ClauseVivifier.h"

//#define VERBOSE_DEBUG
#ifdef VERBOSE_DEBUG
#define BIT_MORE_VERBOSITY
#endif

//#define BIT_MORE_VERBOSITY

using namespace CMSat;

Subsumer::Subsumer(Solver& s):
    solver(s)
    , totalTime(0.0)
    , numElimed(0)
    , numCalls(1)
{
}

/**
@brief Extends the model to include eliminated variables

Adds the clauses to the parameter solver2, and then relies on the
caller to call solver2.solve().

@p solver2 The external solver the variables' clauses are added to
*/
void Subsumer::extendModel(Solver& solver2)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "Subsumer::extendModel(Solver& solver2) called" << std::endl;
    #endif

    assert(checkElimedUnassigned());
    vec<Lit> tmp;
    typedef map<Var, vector<vector<Lit> > > elimType;
    for (elimType::iterator it = elimedOutVar.begin(), end = elimedOutVar.end(); it != end; it++) {
        #ifndef NDEBUG
        Var var = it->first;
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting elimed var: " << var+1 << std::endl;
        #endif
        assert(!solver.decision_var[var]);
        assert(solver.assigns[var] == l_Undef);
        assert(!solver.order_heap.inHeap(var));
        #endif

        for (vector<vector<Lit> >::const_iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            tmp.clear();
            tmp.growTo(it2->size());
            std::copy(it2->begin(), it2->end(), tmp.getData());

            #ifdef VERBOSE_DEBUG
            std::cout << "Reinserting elimed clause: " << tmp << std::endl;;
            #endif

            solver2.addClause(tmp);
            assert(solver2.ok);
        }
    }

    typedef map<Var, vector<std::pair<Lit, Lit> > > elimType2;
    for (elimType2::iterator it = elimedOutVarBin.begin(), end = elimedOutVarBin.end(); it != end; it++) {
        #ifndef NDEBUG
        Var var = it->first;
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting elimed var: " << var+1 << std::endl;
        #endif
        assert(!solver.decision_var[var]);
        assert(solver.assigns[var] == l_Undef);
        assert(!solver.order_heap.inHeap(var));
        #endif

        for (vector<std::pair<Lit, Lit> >::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            tmp.clear();
            tmp.growTo(2);
            tmp[0] = it2->first;
            tmp[1] = it2->second;

            #ifdef VERBOSE_DEBUG
            std::cout << "Reinserting bin clause: " << it2->first << " , " << it2->second << std::endl;
            #endif

            solver2.addClause(tmp);
            assert(solver2.ok);
        }
    }
}

/**
@brief Adds to the solver the clauses representing variable var

This function is useful if a variable was eliminated, but now needs to be
added back again.

@p var The variable to be added back again
*/
bool Subsumer::unEliminate(const Var var)
{
    assert(var_elimed[var]);
    vec<Lit> tmp;
    typedef map<Var, vector<vector<Lit> > > elimType;
    typedef map<Var, vector<std::pair<Lit, Lit> > > elimType2;
    elimType::iterator it = elimedOutVar.find(var);
    elimType2::iterator it2 = elimedOutVarBin.find(var);

    //it MUST have been decision var, otherwise we would
    //never have removed it
    solver.setDecisionVar(var, true);
    var_elimed[var] = false;
    numElimed--;
    #ifdef VERBOSE_DEBUG
    std::cout << "Reinserting normal (non-xor) elimed var: " << var+1 << std::endl;
    #endif

    //If the variable was removed because of
    //pure literal removal (by blocked clause
    //elimination, there are no clauses to re-insert
    if (it == elimedOutVar.end() && it2 == elimedOutVarBin.end()) {
        return solver.ok;
    }

    FILE* backup_libraryCNFfile = solver.libraryCNFFile;
    solver.libraryCNFFile = NULL;

    if (it == elimedOutVar.end()) goto next;
    for (vector<vector<Lit> >::iterator itt = it->second.begin(), end2 = it->second.end(); itt != end2; itt++) {
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting elimed clause: ";
        for (uint32_t i = 0; i < itt->size(); i++) {
            std::cout << (*itt)[i] << " , ";
        }
        std::cout << std::endl;
        #endif
        tmp.clear();
        tmp.growTo(itt->size());
        std::copy(itt->begin(), itt->end(), tmp.getData());
        solver.addClause(tmp);
    }
    elimedOutVar.erase(it);

    next:
    if (it2 == elimedOutVarBin.end()) goto next2;
    for (vector<std::pair<Lit, Lit> >::iterator itt = it2->second.begin(), end2 = it2->second.end(); itt != end2; itt++) {
        tmp.clear();
        tmp.growTo(2);
        tmp[0] = itt->first;
        tmp[1] = itt->second;
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting bin clause: " << itt->first << " , " << itt->second << std::endl;
        #endif
        solver.addClause(tmp);
    }
    elimedOutVarBin.erase(it2);

    next2:
    solver.libraryCNFFile = backup_libraryCNFfile;

    return solver.ok;
}

/**
@brief Backward-subsumption using given clause: helper function

Checks all clauses in the occurrence lists if they are subsumed by ps or not.

The input clause can be learnt. In that case, if it subsumes non-learnt clauses,
it will become non-learnt.

Handles it well if the subsumed clause has a higher activity than the subsuming
clause (will take the max() of the two)

@p ps The clause to use

*/
void Subsumer::subsume0(Clause& ps)
{
    #ifdef VERBOSE_DEBUG
    cout << "subsume0-ing with clause: ";
    ps.plainPrint();
    #endif
    subsume0Happened ret = subsume0Orig(ps, ps.getAbst());

    if (ps.learnt()) {
        if (!ret.subsumedNonLearnt) {
            if (ps.getGlue() > ret.glue)
                ps.setGlue(ret.glue);
            if (ps.getMiniSatAct() < ret.act)
                ps.setMiniSatAct(ret.act);
        } else {
            solver.nbCompensateSubsumer++;
            ps.makeNonLearnt();
        }
    }
}

/**
@brief Backward-subsumption using given clause

@note Use helper function

@param ps The clause to use to backward-subsume
@param[in] abs The abstraction of the clause
@return Subsumed anything? If so, what was the max activity? Was it non-learnt?
*/
template<class T>
Subsumer::subsume0Happened Subsumer::subsume0Orig(const T& ps, uint32_t abs)
{
    subsume0Happened ret;
    ret.subsumedNonLearnt = false;
    ret.glue = std::numeric_limits<uint32_t>::max();
    ret.act = std::numeric_limits< float >::min();

    vec<ClauseSimp> subs;
    findSubsumed(ps, abs, subs);
    for (uint32_t i = 0; i < subs.size(); i++){
        #ifdef VERBOSE_DEBUG
        cout << "-> subsume0 removing:";
        subs[i].clause->plainPrint();
        #endif

        Clause* tmp = subs[i].clause;
        if (tmp->learnt()) {
            ret.glue = std::min(ret.glue, tmp->getGlue());
            ret.act = std::max(ret.act, tmp->getMiniSatAct());
        } else {
            ret.subsumedNonLearnt = true;
        }
        unlinkClause(subs[i]);
    }

    return ret;
}

/**
@brief Backward subsumption and self-subsuming resolution

Performs backward subsumption AND
self-subsuming resolution using backward-subsumption

@param[in] ps The clause to use for backw-subsumption and self-subs. resolution
*/
void Subsumer::subsume1(Clause& ps)
{
    vec<ClauseSimp>    subs;
    vec<Lit>           subsLits;
    #ifdef VERBOSE_DEBUG
    cout << "subsume1-ing with clause:";
    ps.plainPrint();
    #endif

    findSubsumed1(ps, ps.getAbst(), subs, subsLits);
    for (uint32_t j = 0; j < subs.size(); j++) {
        if (subs[j].clause == NULL) continue;
        ClauseSimp c = subs[j];
        if (subsLits[j] == lit_Undef) {
            if (ps.learnt()) {
                if (c.clause->learnt()) ps.takeMaxOfStats(*c.clause);
                else {
                    solver.nbCompensateSubsumer++;
                    ps.makeNonLearnt();
                }
            }
            unlinkClause(c);
        } else {
            strenghten(c, subsLits[j]);
            if (!solver.ok) return;
        }
    }
}

bool Subsumer::subsume1(vec<Lit>& ps, const bool wasLearnt)
{
    vec<ClauseSimp>    subs;
    vec<Lit>           subsLits;
    bool toMakeNonLearnt = false;

    findSubsumed1(ps, calcAbstraction(ps), subs, subsLits);
    for (uint32_t j = 0; j < subs.size(); j++) {
        if (subs[j].clause == NULL) continue;
        ClauseSimp c = subs[j];
        if (subsLits[j] == lit_Undef) {
            if (wasLearnt && !c.clause->learnt()) toMakeNonLearnt = true;
            unlinkClause(c);
        } else {
            strenghten(c, subsLits[j]);
            if (!solver.ok) return false;
        }
    }

    return toMakeNonLearnt;
}

/**
@brief Removes&free-s a clause from everywhere

Removes clause from occurence lists, from Subsumer::clauses, and iter_sets.

If clause is to be removed because the variable in it is eliminated, the clause
is saved in elimedOutVar[] before it is fully removed.

@param[in] c The clause to remove
@param[in] elim If the clause is removed because of variable elmination, this
parameter is different from var_Undef.
*/
void Subsumer::unlinkClause(ClauseSimp c, const Var elim)
{
    Clause& cl = *c.clause;

    for (uint32_t i = 0; i < cl.size(); i++) {
        if (elim != var_Undef) numMaxElim -= occur[cl[i].toInt()].size()/2;
        else {
            numMaxSubsume0 -= occur[cl[i].toInt()].size()/2;
            numMaxSubsume1 -= occur[cl[i].toInt()].size()/2;
        }
        maybeRemove(occur[cl[i].toInt()], &cl);
        touchedVars.touch(cl[i], cl.learnt());
    }

    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_sets.size(); i++) {
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }

    // Remove clause from clause touched set:
    cl_touched.exclude(c);

    //Compensate if removing learnt
    if (cl.learnt()) solver.nbCompensateSubsumer++;

    if (elim != var_Undef) {
        assert(!cl.learnt());
        #ifdef VERBOSE_DEBUG
        std::cout << "Eliminating non-bin clause: " << *c.clause << std::endl;
        std::cout << "On variable: " << elim+1 << std::endl;
        #endif //VERBOSE_DEBUG
        vector<Lit> lits(c.clause->size());
        std::copy(c.clause->getData(), c.clause->getDataEnd(), lits.begin());
        elimedOutVar[elim].push_back(lits);
    } else {
        clauses_subsumed++;
    }
    solver.clauseAllocator.clauseFree(c.clause);

    clauses[c.index].clause = NULL;
}


/**
@brief Cleans clause from false literals

This does NOT re-implement the feature of  ClauseCleaner because
here we need to remove the literals from the occurrence lists as well. Further-
more, we need propagate if needed, which is never assumed to be a need in
ClauseCleaner since there the clauses are always attached to the watch-
lists.

@param ps Clause to be cleaned
*/
bool Subsumer::cleanClause(Clause& ps)
{
    bool retval = false;

    Lit *i = ps.getData();
    Lit *j = i;
    for (Lit *end = ps.getDataEnd(); i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }
        if (val == l_False) {
            removeW(occur[i->toInt()], &ps);
            numMaxSubsume1 -= occur[i->toInt()].size()/2;
            touchedVars.touch(*i, ps.learnt());
            continue;
        }
        if (val == l_True) {
            *j++ = *i;
            retval = true;
            continue;
        }
        assert(false);
    }
    ps.shrink(i-j);

    return retval;
}

bool Subsumer::cleanClause(vec<Lit>& ps) const
{
    bool retval = false;

    Lit *i = ps.getData();
    Lit *j = i;
    for (Lit *end = ps.getDataEnd(); i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }
        if (val == l_False)
            continue;
        if (val == l_True) {
            *j++ = *i;
            retval = true;
            continue;
        }
        assert(false);
    }
    ps.shrink(i-j);

    return retval;
}

/**
@brief Removes a literal from a clause

May return with solver.ok being FALSE, and may set&propagate variable values.

@param c Clause to be cleaned of the literal
@param[in] toRemoveLit The literal to be removed from the clause
*/
void Subsumer::strenghten(ClauseSimp& c, const Lit toRemoveLit)
{
    #ifdef VERBOSE_DEBUG
    cout << "-> Strenghtening clause :";
    c.clause->plainPrint();
    cout << " with lit: " << toRemoveLit << std::endl;
    #endif

    literals_removed++;
    c.clause->strengthen(toRemoveLit);
    removeW(occur[toRemoveLit.toInt()], c.clause);
    numMaxSubsume1 -= occur[toRemoveLit.toInt()].size()/2;
    touchedVars.touch(toRemoveLit, c.clause->learnt());

    if (cleanClause(*c.clause)) {
        unlinkClause(c);
        c.clause = NULL;
        return;
    }

    switch (c.clause->size()) {
        case 0:
            #ifdef VERBOSE_DEBUG
            std::cout << "Strenghtened clause to 0-size -> UNSAT"<< std::endl;
            #endif //VERBOSE_DEBUG
            solver.ok = false;
            break;
        case 1: {
            handleSize1Clause((*c.clause)[0]);
            unlinkClause(c);
            c.clause = NULL;
            break;
        }
        case 2: {
            solver.attachBinClause((*c.clause)[0], (*c.clause)[1], (*c.clause).learnt());
            solver.numNewBin++;
            solver.dataSync->signalNewBinClause(*c.clause);
            clBinTouched.push_back(NewBinaryClause((*c.clause)[0], (*c.clause)[1], (*c.clause).learnt()));
            unlinkClause(c);
            c.clause = NULL;
            break;
        }
        default:
            cl_touched.add(c);
    }
}

bool Subsumer::handleClBinTouched()
{
    assert(solver.ok);
    uint32_t clauses_subsumed_before = clauses_subsumed;
    uint32_t literals_removed_before = literals_removed;
    uint32_t clBinSize = 0;

    vec<Lit> lits(2);
    for (list<NewBinaryClause>::const_iterator it = clBinTouched.begin(); it != clBinTouched.end(); it++) {
        lits[0] = it->lit1;
        lits[1] = it->lit2;
        const bool learnt = it->learnt;

        if (subsume1(lits, learnt)) {
            //if we can't find it, that must be because it has been made non-learnt
            //note: if it has been removed through elimination, it must't
            //be able to subsume any non-learnt clauses, so we never enter here
            if (findWBin(solver.watches, lits[0], lits[1], true)) {
                findWatchedOfBin(solver.watches, lits[0], lits[1], learnt).setLearnt(false);
                findWatchedOfBin(solver.watches, lits[1], lits[0], learnt).setLearnt(false);
            }
        }
        if (!solver.ok) return false;
        clBinSize++;
    }
    clBinTouched.clear();

    if (solver.conf.verbosity >= 3) {
        std::cout << "c subs-w-newbins " << clauses_subsumed - clauses_subsumed_before
        << " lits rem " << literals_removed - literals_removed_before
        << " went through: " << clBinSize << std::endl;
    }

    return true;
}

/**
@brief Handles if a clause became 1-long (unitary)

Either sets&propagates the value, ignores the value (if already set),
or sets solver.ok = FALSE

@param[in] lit The single literal the clause has
*/
inline void Subsumer::handleSize1Clause(const Lit lit)
{
    if (solver.value(lit) == l_False) {
        solver.ok = false;
    } else if (solver.value(lit) == l_Undef) {
        solver.uncheckedEnqueue(lit);
        solver.ok = solver.propagate<false>().isNULL();
    } else {
        assert(solver.value(lit) == l_True);
    }
}

/**
@brief Executes subsume1() recursively on all clauses

This function requires cl_touched to have been set. Then, it manages cl_touched.
The clauses are called to perform subsume1() or subsume0() when appropriate, and
when there is enough numMaxSubume1 and numMaxSubume0 is available.
*/
bool Subsumer::subsume0AndSubsume1()
{
    CSet s0, s1;

    uint32_t clTouchedTodo = 2000;
    if (addedClauseLits > 3000000) clTouchedTodo /= 2;
    if (addedClauseLits > 10000000) clTouchedTodo /= 4;

    registerIteration(s0);
    registerIteration(s1);
    vec<ClauseSimp> remClTouched;

    // Fixed-point for 1-subsumption:
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  cl_touched.nElems() = " << cl_touched.nElems() << std::endl;
    #endif
    while ((cl_touched.nElems() > 10) && numMaxSubsume0 > 0) {
        #ifdef VERBOSE_DEBUG
        std::cout << "c  -- subsume0AndSubsume1() round --" << std::endl;
        std::cout << "c  cl_touched.nElems() = " << cl_touched.nElems() << std::endl;
        std::cout << "c  clauses.size() = " << clauses.size() << std::endl;
        std::cout << "c  numMaxSubsume0:" << numMaxSubsume0 << std::endl;
        std::cout << "c  numMaxSubsume1:" << numMaxSubsume1 << std::endl;
        std::cout << "c  numMaxElim:" << numMaxElim << std::endl;
        #endif //VERBOSE_DEBUG

        uint32_t s1Added = 0;
        const bool doSubs1Next = (numMaxSubsume1 > 0);
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause == NULL) continue;
            Clause& cl = *it->clause;

            if (s1Added >= clTouchedTodo) {
                break;
            }

            s0.add(*it);
            s1Added += s1.add(*it);
            bool unset = true;

            for (uint32_t j = 0; j < cl.size(); j++) {
                if (!ol_seenPos[cl[j].toInt()]) {
                    vec<ClauseSimp>& occs = occur[(cl[j]).toInt()];
                    for (uint32_t k = 0; k < occs.size(); k++) {
                        if (s1Added >= clTouchedTodo) {
                            unset = false;
                            break;
                        }
                        s0.add(occs[k]);
                    }
                }
                ol_seenPos[cl[j].toInt()] = 1;

                if (s1Added >= clTouchedTodo) {
                    unset = false;
                    break;
                }

                if (!ol_seenNeg[(~cl[j]).toInt()]) {
                    vec<ClauseSimp>& occs = occur[(~cl[j]).toInt()];
                    for (uint32_t k = 0; k < occs.size(); k++) {
                        if (s1Added >= clTouchedTodo) {
                            unset = false;
                            break;
                        }

                        s1Added += s1.add(occs[k]);
                    }
                }
                ol_seenNeg[(~cl[j]).toInt()] = 1;

                if (s1Added >= clTouchedTodo) {
                    unset = false;
                    break;
                }
            }

            remClTouched.push(*it);
            if (doSubs1Next && unset)
                it->clause->unsetChanged();
        }
        //std::cout << "s0.nElems(): " << s0.nElems() << std::endl;
        //std::cout << "s1.nElems(): " << s1.nElems() << std::endl;

        for (uint32_t i = 0; i < remClTouched.size(); i++) {
            cl_touched.exclude(remClTouched[i]);
        }
        remClTouched.clear();

        for (CSet::iterator it = s0.begin(), end = s0.end(); it != end; ++it) {
            if (it->clause == NULL) continue;
            subsume0(*it->clause);
        }
        s0.clear();

        if (doSubs1Next) {
            for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
                if (it->clause == NULL) continue;
                subsume1(*it->clause);
                if (!solver.ok) goto end;
            }
            s1.clear();
        }

        if (!handleClBinTouched()) goto end;
    }
    cl_touched.clear();
    end:

    unregisterIteration(s1);
    unregisterIteration(s0);

    return solver.ok;
}

/**
@brief Links in a clause into the occurrence lists and the clauses[]

Increments clauseID

@param[in] cl The clause to link in
*/
ClauseSimp Subsumer::linkInClause(Clause& cl)
{
    ClauseSimp c(&cl, clauseID++);
    clauses.push(c);
    for (uint32_t i = 0; i < cl.size(); i++) {
        occur[cl[i].toInt()].push(c);
        touchedVars.touch(cl[i], cl.learnt());
        if (cl.getChanged()) {
            ol_seenPos[cl[i].toInt()] = 0;
            ol_seenNeg[(~cl[i]).toInt()] = 0;
        }
    }
    if (cl.getChanged())
        cl_touched.add(c);

    return c;
}

/**
@brief Adds clauses from the solver to here, and removes them from the solver

Which clauses are needed can be controlled by the parameters

@param[in] cs The clause-set to use, e.g. solver.binaryClauses, solver.learnts
@param[in] alsoLearnt Also add learnt clauses?
@param[in] addBinAndAddToCL If set to FALSE, binary clauses are not added, and
clauses are never added to the cl_touched set.
*/
uint64_t Subsumer::addFromSolver(vec<Clause*>& cs)
{
    uint64_t numLitsAdded = 0;
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end = i + cs.size(); i !=  end; i++) {
        if (i+1 != end) __builtin_prefetch(*(i+1));

        linkInClause(**i);
        numLitsAdded += (*i)->size();
    }
    cs.shrink(i-j);

    return numLitsAdded;
}

/**
@brief Frees memory occupied by occurrence lists
*/
void Subsumer::freeMemory()
{
    for (uint32_t i = 0; i < occur.size(); i++) {
        occur[i].clear(true);
    }
}

/**
@brief Adds clauses from here, back to the solver
*/
void Subsumer::addBackToSolver()
{
    assert(solver.clauses.size() == 0);
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause == NULL) continue;
        assert(clauses[i].clause->size() > 2);

        if (clauses[i].clause->learnt())
            solver.learnts.push(clauses[i].clause);
        else
            solver.clauses.push(clauses[i].clause);
    }
}

/**
@brief Remove clauses from input that contain eliminated variables

Used to remove learnt clauses that still reference a variable that has been
eliminated.
*/
void Subsumer::removeWrong(vec<Clause*>& cs)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end =  i + cs.size(); i != end; i++) {
        Clause& c = **i;
        if (!c.learnt())  {
            *j++ = *i;
            continue;
        }
        bool remove = false;
        for (Lit *l = c.getData(), *end2 = l+c.size(); l != end2; l++) {
            if (var_elimed[l->var()]) {
                remove = true;
                //solver.detachClause(c);
                solver.clauseAllocator.clauseFree(&c);
                break;
            }
        }
        if (!remove)
            *j++ = *i;
    }
    cs.shrink(i-j);
}

void Subsumer::removeWrongBinsAndAllTris()
{
    uint32_t numRemovedHalfLearnt = 0;
    uint32_t wsLit = 0;
    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++, wsLit++) {
        Lit lit = ~Lit::toLit(wsLit);
        vec<Watched>& ws = *it;

        vec<Watched>::iterator i = ws.getData();
        vec<Watched>::iterator j = i;
        for (vec<Watched>::iterator end2 = ws.getDataEnd(); i != end2; i++) {
            if (i->isTriClause()) continue;

            if (i->isBinary()
                && (var_elimed[lit.var()] || var_elimed[i->getOtherLit().var()])
                ) {
                assert(i->getLearnt());
                numRemovedHalfLearnt++;
            } else {
                *j++ = *i;
            }
        }
        ws.shrink_(i - j);
    }

    assert(numRemovedHalfLearnt % 2 == 0);
    solver.learnts_literals -= numRemovedHalfLearnt;
    solver.numBins -= numRemovedHalfLearnt/2;
}

/**
@brief Fills the vector cannot_eliminate

Variables that are:
* also present in XOR-clauses, or
* have been replaced
cannot be eliminated. This is enforced by the vector cannot_elimnate
*/
void Subsumer::fillCannotEliminate()
{
    std::fill(cannot_eliminate.getData(), cannot_eliminate.getDataEnd(), false);
    for (uint32_t i = 0; i < solver.xorclauses.size(); i++) {
        const XorClause& c = *solver.xorclauses[i];
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }

    for (Var var = 0; var < solver.nVars(); var++) {
        cannot_eliminate[var] |= solver.varReplacer->cannot_eliminate[var];
    }

    #ifdef VERBOSE_DEBUG
    uint32_t tmpNum = 0;
    for (uint32_t i = 0; i < cannot_eliminate.size(); i++)
        if (cannot_eliminate[i])
            tmpNum++;
    std::cout << "Cannot eliminate num:" << tmpNum << std::endl;
    #endif
}

/**
@brief Subsumes&strenghtens normal clauses with (non-existing) binary clauses

First, it backward-subsumes and performs self-subsuming resolution using binary
clauses on non-binary clauses. Then, it generates non-existing binary clauses
(that could exist, but would be redundant), and performs self-subsuming
resolution with them on the normal clauses using \function subsume0BIN().
*/
/*bool Subsumer::subsumeWithBinTri()
{
    assert(solver.ok);

    double mytime = cpuTime();
    uint32_t subsumed_bin = 0;
    uint32_t subsumed_tri = 0;
    uint32_t lit_rem_bin = 0;
    uint32_t lit_rem_tri = 0;
    if (!subsumeWithBinTri(solver.clauses, false, subsumed_bin, subsumed_tri, lit_rem_bin, lit_rem_tri))
        return false;

    if (!subsumeWithBinTri(solver.learnts, true, subsumed_bin, subsumed_tri, lit_rem_bin, lit_rem_tri))
        return false;

    if (solver.conf.verbosity > 0) {
        std::cout
        << "c subs-w-b: " << subsumed_bin
        << " subs-w-t: " << subsumed_tri
        << " lit-rem-w-b: " << lit_rem_bin
        << " lit-rem-w-t: " << lit_rem_tri
        << " T: " << std::fixed << std::setprecision(2) << (cpuTime() - mytime)
        << std::endl;
    }
    return true;
}

bool Subsumer::subsumeWithBinTri(
    vec<Clause*>& cls
    , bool learnt
    , uint32_t& subsumed_bin_num
    , uint32_t& subsumed_tri_num
    , uint32_t& lit_rem_bin
    , uint32_t& lit_rem_tri
) {
    //Temporaries
    vector<Lit> lits_set;
    vector<char> seen_tmp2;
    seen_tmp2.resize(solver.nVars()*2);
    uint32_t to_remove_bin = 0;
    uint32_t to_remove_tri = 0;

    Clause** cit = cls.getData();
    Clause** cit2 =  cit;
    Clause** cend = cls.getDataEnd();

    for(; cit2 != cend; cit2++) {
        Clause& c = **cit2;

        //Set up seen_tmp
        lits_set.resize(c.size());
        for(size_t i = 0; i < c.size(); i++) {
            seen_tmp[c[i].toInt()] = 1;
            seen_tmp2[c[i].toInt()] = 1;
            lits_set[i] = c[i];
        }

        bool subsumed = false;


        if (subsumed) {
#ifdef VERBOSE_DEBUG
            std::cout << "Removing: ";
            c.plainPrint();
#endif
            solver.removeClause(c);
        } else if (to_remove_bin > 0 || to_remove_tri > 0) {
            lit_rem_bin += to_remove_bin;
            lit_rem_tri += to_remove_tri;
            solver.detachClause(c);

#ifdef VERBOSE_DEBUG
            std::cout << "Detached clause: (ptr: " << (&c) << " ) ";
            c.plainPrint();;
#endif

            vec<Lit> lits;
            for(size_t i = 0; i < c.size(); i++) {
                if (seen_tmp2[c[i].toInt()])
                    lits.push(c[i]);
            }

            Clause *c2 = solver.addClauseInt(lits, c.learnt(), c.getGlue(), c.getMiniSatAct());
            solver.clauseAllocator.clauseFree(&c);
            if (c2 != NULL) {
                *cit++ = c2;
            }

            if (!solver.ok) {
                break;
            }
        } else {
            *cit++ = *cit2;
        }

        for(vector<Lit>::const_iterator it = lits_set.begin(), end = lits_set.end(); it != end; it++) {
            seen_tmp[it->toInt()] = 0;
            seen_tmp2[it->toInt()] = 0;
        }
        lits_set.clear();
        to_remove_bin = 0;
        to_remove_tri = 0;
    }
    cls.shrink(cit2-cit);

    return solver.ok;
}*/

/**
@brief Clears and deletes (almost) everything in this class

Clears touchlists, occurrance lists, clauses, and variable touched lists
*/
void Subsumer::clearAll()
{
    touchedVars.clear();
    clauses.clear();
    cl_touched.clear();
    addedClauseLits = 0;
    for (Var var = 0; var < solver.nVars(); var++) {
        occur[2*var].clear();
        occur[2*var+1].clear();
        ol_seenNeg[2*var    ] = 1;
        ol_seenNeg[2*var + 1] = 1;
        ol_seenPos[2*var    ] = 1;
        ol_seenPos[2*var + 1] = 1;
    }
}

bool Subsumer::eliminateVars()
{
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c VARIABLE ELIMINIATION -- touchedVars size:" << touchedVars.size() << std::endl;
    #endif

    uint32_t vars_elimed = 0;

    vec<Var> order;
    orderVarsForElim(order);

    #ifdef VERBOSE_DEBUG
    std::cout << "c #order size:" << order.size() << std::endl;
    #endif

    uint32_t numtry = 0;
    for (uint32_t i = 0; i < order.size() && numMaxElim > 0 && numMaxElimVars > 0; i++) {
        Var var = order[i];
        if (!cannot_eliminate[var] && solver.decision_var[var]) {
            numtry++;
            if (maybeEliminate(order[i])) {
                if (!solver.ok) return false;
                vars_elimed++;
                numMaxElimVars--;
            }
        }
    }
    numVarsElimed += vars_elimed;

    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  #try to eliminate: " << numtry << std::endl;
    std::cout << "c  #var-elim: " << vars_elimed << std::endl;
    #endif

    return true;
}

void Subsumer::subsumeBinsWithBins()
{
    double myTime = cpuTime();
    uint32_t numBinsBefore = solver.numBins;

    uint32_t wsLit = 0;
    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++, wsLit++) {
        vec<Watched>& ws = *it;
        Lit lit = ~Lit::toLit(wsLit);
        if (ws.size() < 2) continue;

        std::sort(ws.getData(), ws.getDataEnd(), BinSorter());

        vec<Watched>::iterator i = ws.getData();
        vec<Watched>::iterator j = i;

        Lit lastLit = lit_Undef;
        bool lastLearnt = false;
        for (vec<Watched>::iterator end = ws.getDataEnd(); i != end; i++) {
            if (!i->isBinary()) {
                *j++ = *i;
                continue;
            }
            if (i->getOtherLit() == lastLit) {
                //The sorting algorithm prefers non-learnt to learnt, so it is
                //impossible to have non-learnt before learnt
                assert(!(i->getLearnt() == false && lastLearnt == true));

                assert(i->getOtherLit().var() != lit.var());
                removeWBin(solver.watches[(~(i->getOtherLit())).toInt()], lit, i->getLearnt());
                if (i->getLearnt()) solver.learnts_literals -= 2;
                else {
                    solver.clauses_literals -= 2;
                    touchedVars.touch(lit, i->getLearnt());
                    touchedVars.touch(i->getOtherLit(), i->getLearnt());
                }
                solver.numBins--;
            } else {
                lastLit = i->getOtherLit();
                lastLearnt = i->getLearnt();
                *j++ = *i;
            }
        }
        ws.shrink_(i-j);
    }

    if (solver.conf.verbosity  >= 1) {
        std::cout << "c bin-w-bin subsume rem   "
        << std::setw(10) << (numBinsBefore - solver.numBins) << " bins "
        << " time: "
        << std::fixed << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime)
        << " s" << std::endl;
    }
    totalTime += cpuTime() - myTime;
    clauses_subsumed += (numBinsBefore - solver.numBins);
}

/**
@brief Main function in this class

Performs, recursively:
* backward-subsumption
* self-subsuming resolution
* variable elimination

*/
bool Subsumer::simplifyBySubsumption()
{
    if (solver.nClauses() > 50000000
        || solver.clauses_literals > 500000000)  return true;

    double myTime = cpuTime();
    clauseID = 0;
    clearAll();

    //touch all variables
    for (Var var = 0; var < solver.nVars(); var++) {
        if (solver.decision_var[var] && solver.assigns[var] == l_Undef) touchedVars.touch(var);
    }

    if (solver.conf.doReplace && !solver.varReplacer->performReplace(true))
        return false;
    /*if (solver.conf.doSubsWBins && !subsumeWithBinTri())
        return false;*/

    fillCannotEliminate();

    uint32_t expected_size = solver.clauses.size() + solver.learnts.size();
    if (expected_size > 10000000) return solver.ok;

    clauses.reserve(expected_size);
    cl_touched.reserve(expected_size);

    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    solver.clauseCleaner->cleanClauses(solver.learnts, ClauseCleaner::learnts);

    if (solver.clauses.size() < 10000000)
        std::sort(solver.clauses.getData(), solver.clauses.getDataEnd(), sortBySize());
    addedClauseLits += addFromSolver(solver.clauses);

    if (solver.learnts.size() < 300000)
        std::sort(solver.learnts.getData(), solver.learnts.getDataEnd(), sortBySize());
    addedClauseLits += addFromSolver(solver.learnts);

    CompleteDetachReatacher reattacher(solver);
    reattacher.detachNonBinsNonTris(false);
    totalTime += myTime - cpuTime();

    //Do stuff with binaries
    subsumeBinsWithBins();
    numMaxSubsume1 = 500*1000*1000;
    if ((solver.conf.doBlockedClause)
        && solver.conf.doVarElim) {
        numMaxBlockToVisit = (int64_t)800*1000*1000;
        blockedClauseRemoval();
    }

    numMaxSubsume1 = 2*1000*1000*1000;
    //if (solver.conf.doSubsWNonExistBins && !subsWNonExitsBinsFullFull()) return false;
    if (!handleClBinTouched()) return false;

    if (solver.conf.doReplace && solver.conf.doRemUselessBins) {
        UselessBinRemover uselessBinRemover(solver);
        if (!uselessBinRemover.removeUslessBinFull()) return false;
    }

    myTime = cpuTime();
    setLimits();
    clauses_subsumed = 0;
    literals_removed = 0;
    numVarsElimed = 0;
    uint32_t origTrailSize = solver.trail.size();

    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  time until pre-subsume0 clauses and subsume1 2-learnts:" << cpuTime()-myTime << std::endl;
    std::cout << "c  pre-subsumed:" << clauses_subsumed << std::endl;
    std::cout << "c  cl_touched:" << cl_touched.nElems() << std::endl;
    std::cout << "c  clauses:" << clauses.size() << std::endl;
    std::cout << "c  numMaxSubsume0:" << numMaxSubsume0 << std::endl;
    std::cout << "c  numMaxSubsume1:" << numMaxSubsume1 << std::endl;
    std::cout << "c  numMaxElim:" << numMaxElim << std::endl;
    #endif

    do {
        if (!subsume0AndSubsume1()) return false;

        if (!solver.conf.doVarElim) break;

        if (!eliminateVars()) return false;

        //subsumeBinsWithBins();
        solver.clauseCleaner->removeSatisfiedBins();
    } while (cl_touched.nElems() > 10);

    if (!solver.ok) return false;

    assert(verifyIntegrity());

    removeWrong(solver.learnts);
    removeWrongBinsAndAllTris();
    removeAssignedVarsFromEliminated();

    solver.order_heap.filter(Solver::VarFilter(solver));

    addBackToSolver();
    if (!reattacher.reattachNonBins()) return false;

    if (solver.conf.verbosity  >= 1) {
        std::cout << "c lits-rem: " << std::setw(9) << literals_removed
        << "  cl-subs: " << std::setw(8) << clauses_subsumed
        << "  v-elim: " << std::setw(6) << numVarsElimed
        << "  v-fix: " << std::setw(4) <<solver.trail.size() - origTrailSize
        << "  time: " << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime) << " s"
        //<< " blkClRem: " << std::setw(5) << numblockedClauseRemoved
        << std::endl;
    }
    totalTime += cpuTime() - myTime;

    solver.testAllClauseAttach();
    return true;
}

/**
@brief Calculate limits for backw-subsumption, var elim, etc.

It is important to have limits, otherwise the time taken to perfom these tasks
could be huge. Furthermore, it seems that there is a benefit in doing these
simplifications slowly, instead of trying to use them as much as possible
from the beginning.
*/
void Subsumer::setLimits()
{
    numMaxSubsume0 = 300*1000*1000;
    numMaxSubsume1 = 30*1000*1000;

    numMaxElim = 500*1000*1000;
    numMaxElim *= 6;

    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c addedClauseLits: " << addedClauseLits << std::endl;
    #endif

    if (addedClauseLits < 5000000) {
        numMaxElim *= 2;
        numMaxSubsume0 *= 2;
        numMaxSubsume1 *= 2;
    }

    if (addedClauseLits < 1000000) {
        numMaxElim *= 2;
        numMaxSubsume0 *= 2;
        numMaxSubsume1 *= 2;
    }

    numMaxElimVars = (uint64_t) (((double)solver.order_heap.size()*0.3) * sqrt((double)numCalls));

    if (solver.order_heap.size() > 200000)
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 3.5 * (0.8+(double)(numCalls)/4.0));
    else
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 1.5 * (0.8+(double)(numCalls)/4.0));

    if (!solver.conf.doSubsume1)
        numMaxSubsume1 = 0;


    numCalls++;

    //For debugging

    //numMaxSubsume0 = 0;
    //numMaxSubsume1 = 0;
    //numMaxSubsume0 = std::numeric_limits<int64_t>::max();
    //numMaxSubsume1 = std::numeric_limits<int64_t>::max();
    //numMaxElimVars = std::numeric_limits<int32_t>::max();
    //numMaxElim     = std::numeric_limits<int64_t>::max();

    //numMaxBlockToVisit = std::numeric_limits<int64_t>::max();
    //numMaxBlockVars = std::numeric_limits<uint32_t>::max();
}

/*bool Subsumer::subsWNonExitsBinsFullFull()
{
    double myTime = cpuTime();
    clauses_subsumed = 0;
    literals_removed = 0;
    for (vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++) {
        if (it->size() < 2) continue;
        std::sort(it->getData(), it->getDataEnd(), BinSorter2());
    }
    uint32_t oldTrailSize = solver.trail.size();
    if (!subsWNonExistBinsFull()) return false;
    if (solver.conf.verbosity  >= 1) {
        std::cout << "c Subs w/ non-existent bins: " << std::setw(6) << clauses_subsumed
        << " l-rem: " << std::setw(6) << literals_removed
        << " v-fix: " << std::setw(5) << solver.trail.size() - oldTrailSize
        << " done: " << std::setw(6) << doneNum
        << " time: " << std::fixed << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime) << " s"
        << std::endl;
    }
    totalTime += cpuTime() - myTime;
    return true;
}

#define MAX_BINARY_PROP 60000000

bool Subsumer::subsWNonExistBinsFull()
{
    uint64_t oldProps = solver.propagations;
    uint64_t maxProp = MAX_BINARY_PROP*7;
    toVisitAll.clear();
    toVisitAll.growTo(solver.nVars()*2, false);
    extraTimeNonExist = 0;
    OnlyNonLearntBins* onlyNonLearntBins = NULL;
    if (solver.clauses_literals < 10*1000*1000) {
        onlyNonLearntBins = new OnlyNonLearntBins(solver);
        onlyNonLearntBins->fill();
        solver.multiLevelProp = true;
    }

    doneNum = 0;
    uint32_t startFrom = solver.mtrand.randInt(solver.order_heap.size());
    for (uint32_t i = 0; i < solver.order_heap.size(); i++) {
        Var var = solver.order_heap[(startFrom + i) % solver.order_heap.size()];
        if (solver.propagations + extraTimeNonExist*150 > oldProps + maxProp) break;
        if (solver.assigns[var] != l_Undef || !solver.decision_var[var]) continue;
        doneNum++;
        extraTimeNonExist += 5;

        Lit lit(var, true);
        if (onlyNonLearntBins != NULL && onlyNonLearntBins->getWatchSize(lit) == 0) goto next;
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntilLight();
            solver.uncheckedEnqueue(~lit);
            solver.ok = solver.propagate<false>().isNULL();
            if (!solver.ok) return false;
            continue;
        }
        extraTimeNonExist += 10;
        next:

        //in the meantime it could have got assigned
        if (solver.assigns[var] != l_Undef) continue;
        lit = ~lit;
        if (onlyNonLearntBins != NULL && onlyNonLearntBins->getWatchSize(lit) == 0) continue;
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntilLight();
            solver.uncheckedEnqueue(~lit);
            solver.ok = solver.propagate<false>().isNULL();
            if (!solver.ok) return false;
            continue;
        }
        extraTimeNonExist += 10;
    }

    if (onlyNonLearntBins) delete onlyNonLearntBins;

    return true;
}

bool Subsumer::subsWNonExistBins(const Lit& lit, OnlyNonLearntBins* onlyNonLearntBins)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "subsWNonExistBins called with lit " << lit << std::endl;
    #endif //VERBOSE_DEBUG
    toVisit.clear();
    solver.newDecisionLevel();
    solver.uncheckedEnqueueLight(lit);
    bool failed;
    if (onlyNonLearntBins == NULL)
        failed = (!solver.propagateNonLearntBin().isNULL());
    else
        failed = !onlyNonLearntBins->propagate();
    if (failed) return false;
    uint32_t abst = 0;

    assert(solver.decisionLevel() > 0);
    for (int sublevel = solver.trail.size()-1; sublevel > (int)solver.trail_lim[0]; sublevel--) {
        Lit x = solver.trail[sublevel];
        toVisit.push(x);
        abst |= 1 << (x.var() & 31);
        toVisitAll[x.toInt()] = true;
    }
    solver.cancelUntilLight();
    subsume0BIN(~lit, toVisitAll, abst);

    for (uint32_t i = 0; i < toVisit.size(); i++)
        toVisitAll[toVisit[i].toInt()] = false;

    return solver.ok;
}

void Subsumer::subsume0BIN(const Lit lit1, const vec<char>& lits, const uint32_t abst)
{
    vec<ClauseSimp> subs;
    vec<ClauseSimp> subs2;
    vec<Lit> subs2Lit;

    vec<ClauseSimp>& cs = occur[lit1.toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end) __builtin_prefetch((it+1)->clause);
        if (it->clause == NULL) continue;

        Clause& c = *it->clause;
        if ((c.getAbst() & abst) == 0) continue;
        extraTimeNonExist += c.size()*2;
        bool removed = false;
        bool removedLit = false;
        for (uint32_t i = 0; i < c.size(); i++) {
            if (lits[c[i].toInt()]) {
                subs.push(*it);
                removed = true;
                break;
            }

            if (!removedLit && lits[(~c[i]).toInt()]) {
                subs2.push(*it);
                subs2Lit.push(c[i]);
                removedLit = true;
            }
        }

        if (removed && removedLit) {
            subs2.pop();
            subs2Lit.pop();
        }
    }

    for (uint32_t i = 0; i < subs.size(); i++){
        unlinkClause(subs[i]);
    }

    for (uint32_t i = 0; i < subs2.size(); i++) {
        strenghten(subs2[i], subs2Lit[i]);
        if (!solver.ok) break;
    }

    #ifdef VERBOSE_DEBUG
    if (!solver.ok) {
        std::cout << "solver.ok is false when returning from subsume0BIN()" << std::endl;
    }
    #endif //VERBOSE_DEBUG
}*/



/**
@brief Remove variables from var_elimed if it has been set

While doing, e.g. self-subsuming resolution, it might happen that the variable
that we JUST eliminated has been assigned a value. This could happen for example
if due to clause-cleaning some variable value got propagated that we just set.
Therefore, we must check at the very end if any variables that we eliminated
got set, and if so, the clauses linked to these variables can be fully removed
from elimedOutVar[].
*/
void Subsumer::removeAssignedVarsFromEliminated()
{
    for (Var var = 0; var < var_elimed.size(); var++) {
        if (var_elimed[var] && solver.assigns[var] != l_Undef) {
            var_elimed[var] = false;
            solver.setDecisionVar(var, true);
            numElimed--;

            map<Var, vector<vector<Lit> > >::iterator it = elimedOutVar.find(var);
            if (it != elimedOutVar.end()) elimedOutVar.erase(it);

            map<Var, vector<std::pair<Lit, Lit> > >::iterator it2 = elimedOutVarBin.find(var);
            if (it2 != elimedOutVarBin.end()) elimedOutVarBin.erase(it2);
        }
    }
}

/**
@brief Finds clauses that are backward-subsumed by given clause

Only handles backward-subsumption. Uses occurrence lists

@param[in] ps The clause to backward-subsume with.
@param[in] abs Abstraction of the clause ps
@param[out] out_subsumed The set of clauses subsumed by this clause
*/
template<class T>
void Subsumer::findSubsumed(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed: " << ps << std::endl;
    #endif

    for (uint32_t i = 0; i != ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 1;

    uint32_t min_i = 0;
    for (uint32_t i = 1; i < ps.size(); i++){
        if (occur[ps[i].toInt()].size() < occur[ps[min_i].toInt()].size())
            min_i = i;
    }

    vec<ClauseSimp>& cs = occur[ps[min_i].toInt()];
    numMaxSubsume0 -= cs.size()*10 + 5;
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end) __builtin_prefetch((it+1)->clause);

        if (it->clause != (Clause*)&ps
            && subsetAbst(abs, it->clause->getAbst())
            && ps.size() <= it->clause->size()) {
                numMaxSubsume0 -= (*it).clause->size() + ps.size();
                if (subset(ps.size(), *it->clause)) {
                out_subsumed.push(*it);
                #ifdef VERBOSE_DEBUG
                cout << "subsumed: ";
                it->clause->plainPrint();
                #endif
            }
        }
    }

    for (uint32_t i = 0; i != ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 0;
}

/**
@brief Checks if clauses are subsumed or could be strenghtened with given clause

Checks if:
* any clause is subsumed with given clause
* the given clause could perform self-subsuming resolution on any other clause

Only takes into consideration clauses that are in the occurrence lists.

@param[in] ps The clause to perform the above listed algos with
@param[in] abs The abstraction of clause ps
@param[out] out_subsumed The clauses that could be modified by ps
@param[out] out_lits Defines HOW these clauses could be modified. By removing
literal, or by subsumption (in this case, there is lit_Undef here)
*/
template<class T>
void Subsumer::findSubsumed1(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed, vec<Lit>& out_lits)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed1: " << ps << std::endl;
    #endif

    Var minVar = var_Undef;
    uint32_t bestSize = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < ps.size(); i++){
        uint32_t newSize = occur[ps[i].toInt()].size()+ occur[(~ps[i]).toInt()].size();
        if (newSize < bestSize) {
            minVar = ps[i].var();
            bestSize = newSize;
        }
    }
    assert(minVar != var_Undef);

    numMaxSubsume1 -= bestSize*10 + 10;
    fillSubs(ps, abs, out_subsumed, out_lits, Lit(minVar, true));
    fillSubs(ps, abs, out_subsumed, out_lits, Lit(minVar, false));
}

/**
@brief Helper function for findSubsumed1

Used to avoid duplication of code
*/
template<class T>
void inline Subsumer::fillSubs(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed, vec<Lit>& out_lits, const Lit lit)
{
    Lit litSub;
    vec<ClauseSimp>& cs = occur[lit.toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++) {
        if (it+1 != end) __builtin_prefetch((it+1)->clause);

        if (it->clause != (Clause*)&ps
            && subsetAbst(abs, it->clause->getAbst())
            && ps.size() <= it->clause->size()) {
            numMaxSubsume1 -= (*it).clause->size() + ps.size();
            litSub = subset1(ps, *it->clause);
            if (litSub != lit_Error) {
                out_subsumed.push(*it);
                out_lits.push(litSub);
                #ifdef VERBOSE_DEBUG
                if (litSub == lit_Undef) cout << "subsume0-d: ";
                else cout << "subsume1-ed (lit: " << litSub << "): ";
                it->clause->plainPrint();
                #endif
            }
        }
    }
}


void Subsumer::removeClausesHelper(vec<ClAndBin>& todo, const Var var, std::pair<uint32_t, uint32_t>& removed)
{
     pair<uint32_t, uint32_t>  tmp;
     for (uint32_t i = 0; i < todo.size(); i++) {
        ClAndBin& c = todo[i];
        if (!c.isBin) {
            unlinkClause(c.clsimp, var);
        } else {
            #ifdef VERBOSE_DEBUG
            std::cout << "Eliminating bin clause: " << c.lit1 << " , " << c.lit2 << std::endl;
            std::cout << "On variable: " << var+1 << std::endl;
            #endif
            assert(var == c.lit1.var() || var == c.lit2.var());
            tmp = removeWBinAll(solver.watches[(~c.lit1).toInt()], c.lit2);
            //assert(tmp.first > 0 || tmp.second > 0);
            removed.first += tmp.first;
            removed.second += tmp.second;

            tmp = removeWBinAll(solver.watches[(~c.lit2).toInt()], c.lit1);
            //assert(tmp.first > 0 || tmp.second > 0);
            removed.first += tmp.first;
            removed.second += tmp.second;

            elimedOutVarBin[var].push_back(std::make_pair(c.lit1, c.lit2));
            touchedVars.touch(c.lit1, false);
            touchedVars.touch(c.lit2, false);
        }
    }
}

/**
@brief Used for variable elimination

Migrates clauses in poss to ps, and negs to ns
Also unlinks ass clauses is ps and ns. This is special unlinking, since it
actually saves the clauses for later re-use when extending the model, or re-
introducing the eliminated variables.

@param[in] poss The occurrence list of var where it is positive
@param[in] negs The occurrence list of var where it is negavite
@param[out] ps Where thre clauses from poss have been moved
@param[out] ns Where thre clauses from negs have been moved
@param[in] var The variable that is being eliminated
*/
void Subsumer::removeClauses(vec<ClAndBin>& posAll, vec<ClAndBin>& negAll, const Var var)
{
    pair<uint32_t, uint32_t> removed;
    removed.first = 0;
    removed.second = 0;

    removeClausesHelper(posAll, var, removed);
    removeClausesHelper(negAll, var, removed);

    solver.learnts_literals -= removed.first;
    solver.clauses_literals -= removed.second;
    solver.numBins -= (removed.first + removed.second)/2;
}

uint32_t Subsumer::numNonLearntBins(const Lit lit) const
{
    uint32_t num = 0;
    const vec<Watched>& ws = solver.watches[(~lit).toInt()];
    for (vec<Watched>::const_iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
        if (it->isBinary() && !it->getLearnt()) num++;
    }

    return num;
}

void Subsumer::fillClAndBin(vec<ClAndBin>& all, vec<ClauseSimp>& cs, const Lit lit)
{
    for (uint32_t i = 0; i < cs.size(); i++) {
        if (!cs[i].clause->learnt()) all.push(ClAndBin(cs[i]));
    }

    const vec<Watched>& ws = solver.watches[(~lit).toInt()];
    for (vec<Watched>::const_iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
        if (it->isBinary() &&!it->getLearnt()) all.push(ClAndBin(lit, it->getOtherLit()));
    }
}

/**
@brief Tries to eliminate variable

Tries to eliminate a variable. It uses heuristics to decide whether it's a good
idea to eliminate a variable or not.

@param[in] var The variable that is being eliminated
@return TRUE if variable was eliminated
*/
bool Subsumer::maybeEliminate(const Var var)
{
    assert(!var_elimed[var]);
    assert(!cannot_eliminate[var]);
    assert(solver.decision_var[var]);
    if (solver.value(var) != l_Undef) return false;

    Lit lit = Lit(var, false);

    //Only exists in binary clauses -- don't delete it then
    /*if (occur[lit.toInt()].size() == 0 && occur[(~lit).toInt()].size() == 0)
        return false;*/

    vec<ClauseSimp>& poss = occur[lit.toInt()];
    vec<ClauseSimp>& negs = occur[(~lit).toInt()];
    const uint32_t numNonLearntPos = numNonLearntBins(lit);
    const uint32_t numNonLearntNeg = numNonLearntBins(~lit);
    uint32_t before_literals = numNonLearntNeg*2 + numNonLearntPos*2;

    uint32_t posSize = 0;
    for (uint32_t i = 0; i < poss.size(); i++)
        if (!poss[i].clause->learnt()) {
            posSize++;
            before_literals += poss[i].clause->size();
        }
    posSize += numNonLearntPos;

    uint32_t negSize = 0;
    for (uint32_t i = 0; i < negs.size(); i++)
        if (!negs[i].clause->learnt()) {
            negSize++;
            before_literals += negs[i].clause->size();
        }
    negSize += numNonLearntNeg;

    numMaxElim -= posSize + negSize;

    // Heuristic CUT OFF:
    if (posSize >= 10 && negSize >= 10) return false;

    // Heuristic CUT OFF2:
    if ((posSize >= 3 && negSize >= 3 && before_literals > 300)
        && clauses.size() > 700000)
        return false;
    if ((posSize >= 5 && negSize >= 5 && before_literals > 400)
        && clauses.size() <= 700000 && clauses.size() > 100000)
        return false;
    if ((posSize >= 8 && negSize >= 8 && before_literals > 700)
        && clauses.size() <= 100000)
        return false;

    vec<ClAndBin> posAll, negAll;
    fillClAndBin(posAll, poss, lit);
    fillClAndBin(negAll, negs, ~lit);

    // Count clauses/literals after elimination:
    uint32_t before_clauses = posSize + negSize;
    uint32_t after_clauses = 0;
    vec<Lit> dummy; //to reduce temporary data allocation
    for (uint32_t i = 0; i < posAll.size(); i++) for (uint32_t j = 0; j < negAll.size(); j++){
        // Merge clauses. If 'y' and '~y' exist, clause will not be created.
        dummy.clear();
        const bool ok = merge(posAll[i], negAll[j], lit, ~lit, dummy);
        if (ok){
            after_clauses++;
            if (after_clauses > before_clauses)
                return false;
        }
    }

    //Eliminate
    //removing clauses (both non-learnt and learnt)
    vec<ClauseSimp> tmp1 = poss;
    poss.clear();
    for (uint32_t i = 0; i < tmp1.size(); i++) {
        if (tmp1[i].clause->learnt()) unlinkClause(tmp1[i]);
    }
    vec<ClauseSimp> tmp2 = negs;
    negs.clear();
    for (uint32_t i = 0; i < tmp2.size(); i++) {
        if (tmp2[i].clause->learnt()) unlinkClause(tmp2[i]);
    }

    removeClauses(posAll, negAll, var);

    //check watchlists
    #ifndef NDEBUG
    const vec<Watched>& ws1 = solver.watches[lit.toInt()];
    for (vec<Watched>::const_iterator i = ws1.getData(), end = ws1.getDataEnd(); i != end; i++) {
        assert(i->isTriClause() || (i->isBinary() && i->getLearnt()));
    }
    const vec<Watched>& ws2 = solver.watches[(~lit).toInt()];
    for (vec<Watched>::const_iterator i = ws2.getData(), end = ws2.getDataEnd(); i != end; i++) {
        assert(i->isTriClause() || (i->isBinary() && i->getLearnt()));
    }
    #endif

    for (uint32_t i = 0; i < posAll.size(); i++) for (uint32_t j = 0; j < negAll.size(); j++){
        dummy.clear();
        bool ok = merge(posAll[i], negAll[j], lit, ~lit, dummy);
        if (!ok) continue;

        if (cleanClause(dummy))
            continue;

        #ifdef VERBOSE_DEBUG
        std::cout << "Adding new clause due to varelim: " << dummy << std::endl;
        #endif
        switch (dummy.size()) {
            case 0:
                solver.ok = false;
                break;
            case 1: {
                handleSize1Clause(dummy[0]);
                break;
            }
            case 2: {
                if (findWBin(solver.watches, dummy[0], dummy[1])) {
                    Watched& w = findWatchedOfBin(solver.watches, dummy[0], dummy[1]);
                    if (w.getLearnt()) {
                        w.setLearnt(false);
                        findWatchedOfBin(solver.watches, dummy[1], dummy[0], true).setLearnt(false);
                        solver.learnts_literals -= 2;
                        solver.clauses_literals += 2;
                    }
                } else {
                    solver.attachBinClause(dummy[0], dummy[1], false);
                    solver.numNewBin++;
                }
                if (numMaxSubsume1 > 0)
                    subsume1(dummy, false);
                break;
            }
            default: {
                Clause* cl = solver.clauseAllocator.Clause_new(dummy);
                ClauseSimp c = linkInClause(*cl);
                if (numMaxSubsume1 > 0) subsume1(*c.clause);
                else if (numMaxSubsume0) subsume0(*c.clause);
            }
        }
        if (!solver.ok) return true;
    }

    assert(occur[lit.toInt()].size() == 0 &&  occur[(~lit).toInt()].size() == 0);
    var_elimed[var] = true;
    numElimed++;
    solver.setDecisionVar(var, false);
    return true;
}

/**
@brief Resolves two clauses on a variable

Clause ps must contain without_p
Clause ps must contain without_q
And without_p = ~without_q

@note: 'seen' is assumed to be cleared.

@param[in] var The variable that is being eliminated
@return FALSE if clause is always satisfied ('out_clause' should not be used)
*/
bool Subsumer::merge(const ClAndBin& ps, const ClAndBin& qs, const Lit without_p, const Lit without_q, vec<Lit>& out_clause)
{
    bool retval = true;
    if (ps.isBin) {
        numMaxElim -= 2;
        assert(ps.lit1 == without_p);
        assert(ps.lit2 != without_p);

        seen_tmp[ps.lit2.toInt()] = 1;
        out_clause.push(ps.lit2);
    } else {
        Clause& c = *ps.clsimp.clause;
        numMaxElim -= c.size()*5;
        for (uint32_t i = 0; i < c.size(); i++){
            if (c[i] != without_p){
                seen_tmp[c[i].toInt()] = 1;
                out_clause.push(c[i]);
            }
        }
    }

    if (qs.isBin) {
        numMaxElim -= 2;
        assert(qs.lit1 == without_q);
        assert(qs.lit2 != without_q);

        if (seen_tmp[(~qs.lit2).toInt()]) {
            retval = false;
            goto end;
        }
        if (!seen_tmp[qs.lit2.toInt()])
            out_clause.push(qs.lit2);
    } else {
        Clause& c = *qs.clsimp.clause;
        numMaxElim -= c.size()*5;
        for (uint32_t i = 0; i < c.size(); i++){
            if (c[i] != without_q) {
                if (seen_tmp[(~c[i]).toInt()]) {
                    retval = false;
                    goto end;
                }
                if (!seen_tmp[c[i].toInt()])
                    out_clause.push(c[i]);
            }
        }
    }

    end:
    if (ps.isBin) {
        seen_tmp[ps.lit2.toInt()] = 0;
    } else {
        Clause& c = *ps.clsimp.clause;
        for (uint32_t i = 0; i < c.size(); i++)
            seen_tmp[c[i].toInt()] = 0;
    }

    return retval;
}

/**
@brief Orders variables for elimination

Variables are ordered according to their occurrances. If a variable occurs far
less than others, it should be prioritised for elimination. The more difficult
variables are OK to try later.

@note: Will untouch all variables.

@param[out] order The order to try to eliminate the variables
*/
void Subsumer::orderVarsForElim(vec<Var>& order)
{
    order.clear();
    vec<pair<int, Var> > cost_var;
    for (vector<Var>::const_iterator it = touchedVars.begin(), end = touchedVars.end(); it != end ; it++){
        Lit x = Lit(*it, false);

        //Long non-learnt POS
        uint32_t pos = 0;
        const vec<ClauseSimp>& poss = occur[x.toInt()];
        for (uint32_t i = 0; i < poss.size(); i++)
            if (!poss[i].clause->learnt()) pos++;

        //Long non-learnt NEG
        uint32_t neg = 0;
        const vec<ClauseSimp>& negs = occur[(~x).toInt()];
        for (uint32_t i = 0; i < negs.size(); i++)
            if (!negs[i].clause->learnt()) neg++;

        //Short non-lerants
        //uint32_t nNonLPos = numNonLearntBins(x);
        //uint32_t nNonLNeg = numNonLearntBins(~x);

        //uint32_t cost = pos*neg/2 +  nNonLPos*neg*2 + nNonLNeg*pos*2 + nNonLNeg*nNonLPos*6;
        uint32_t cost = pos*neg * 2 + numNonLearntBins(x) * neg + numNonLearntBins(~x) * pos;

        cost_var.push(std::make_pair(cost, x.var()));
    }
    touchedVars.clear();

    std::sort(cost_var.getData(), cost_var.getDataEnd(), myComp());
    for (uint32_t x = 0; x < cost_var.size(); x++) {
        order.push(cost_var[x].second);
    }
}

/**
@brief Verifies that occurrence lists are OK

Calculates how many occurences are of the varible in clauses[], and if that is
less than occur[var].size(), returns FALSE

@return TRUE if they are OK
*/
bool Subsumer::verifyIntegrity()
{
    vector<uint32_t> occurNum(solver.nVars()*2, 0);

    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause == NULL) continue;
        Clause& c = *clauses[i].clause;
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            occurNum[c[i2].toInt()]++;
    }

    for (uint32_t i = 0; i < occurNum.size(); i++) {
        #ifdef VERBOSE_DEBUG
        std::cout << "occurNum[i]:" << occurNum[i]
        << " occur[i]:" << occur[i].size()
        << "  --- i:" << i << std::endl;
        #endif //VERBOSE_DEBUG

        if (occurNum[i] != occur[i].size()) return false;
    }

    return true;
}

template<class T>
bool Subsumer::allTautology(const T& ps, const Lit lit)
{
    #ifdef VERBOSE_DEBUG
    cout << "allTautology: " << ps << std::endl;
    #endif

    numMaxBlockToVisit -= ps.size()*2;
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        if (*l != ~lit) seen_tmp[l->toInt()] = true;
    }

    bool allIsTautology = true;
    const vec<ClauseSimp>& cs = occur[lit.toInt()];
    const vec<Watched>& ws = solver.watches[(~lit).toInt()];

    for (const ClauseSimp *it = cs.getData(), *end = cs.getDataEnd(); it != end; it++){
        if (it+1 != end) __builtin_prefetch((it+1)->clause);

        const Clause& c = *it->clause;
        numMaxBlockToVisit -= c.size();
        for (const Lit *l = c.getData(), *end2 = c.getDataEnd(); l != end2; l++) {
            if (seen_tmp[(~(*l)).toInt()]) {
                goto next;
            }
        }
        allIsTautology = false;
        break;

        next:;
    }
    if (!allIsTautology) goto end;

    numMaxBlockToVisit -= ws.size();
    for (vec<Watched>::const_iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
        if (!it->isNonLearntBinary()) continue;
        if (seen_tmp[(~it->getOtherLit()).toInt()]) continue;
        else {
            allIsTautology = false;
            break;
        }
    }

    end:
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        seen_tmp[l->toInt()] = false;
    }

    return allIsTautology;
}

void Subsumer::blockedClauseRemoval()
{
    if (numMaxBlockToVisit < 0) return;
    if (solver.order_heap.empty()) return;

    double myTime = cpuTime();
    numblockedClauseRemoved = 0;
    uint32_t numElimedBefore = numElimed;

    touchedBlockedVars = priority_queue<VarOcc, vector<VarOcc>, MyComp>();
    touchedBlockedVarsBool.clear();
    touchedBlockedVarsBool.growTo(solver.nVars(), false);
    for (uint32_t i =  0; i < solver.order_heap.size(); i++) {
        //if (solver.order_heap.size() < 1) break;
        //touchBlockedVar(solver.order_heap[solver.mtrand.randInt(solver.order_heap.size()-1)]);
        touchBlockedVar(solver.order_heap[i]);
    }

    uint32_t triedToBlock = 0;
    while (numMaxBlockToVisit > 0 && !touchedBlockedVars.empty()) {
        VarOcc vo = touchedBlockedVars.top();
        touchedBlockedVars.pop();
        touchedBlockedVarsBool[vo.var] = false;

        if (solver.value(vo.var) != l_Undef
            || !solver.decision_var[vo.var]
            || cannot_eliminate[vo.var])
            continue;

        triedToBlock++;
        Lit lit = Lit(vo.var, false);

        //if (!tryOneSetting(lit)) {
            tryOneSetting(lit);
       // }
    }

    if (solver.conf.verbosity >= 1) {
        std::cout
        << "c spec. var-rem cls: " << std::setw(8) << numblockedClauseRemoved
        << " vars: " << std::setw(6) << numElimed - numElimedBefore
        << " tried: " << std::setw(11) << triedToBlock
        << " T: " << std::fixed << std::setprecision(2) << std::setw(4) << cpuTime() - myTime
        << " s" << std::endl;
    }
}

bool Subsumer::tryOneSetting(const Lit lit)
{
    numMaxBlockToVisit -= occur[lit.toInt()].size();
    for(ClauseSimp *it = occur[lit.toInt()].getData(), *end = occur[lit.toInt()].getDataEnd(); it != end; it++) {
        if (!allTautology(*it->clause, ~lit)) {
            return false;
        }
    }

    vec<Lit> lits(1);
    const vec<Watched>& ws = solver.watches[(~lit).toInt()];
    numMaxBlockToVisit -= ws.size();
    for (vec<Watched>::const_iterator it = ws.getData(), end = ws.getDataEnd(); it != end; it++) {
        if (!it->isNonLearntBinary()) continue;
        lits[0] = it->getOtherLit();
        if (!allTautology(lits, ~lit)) return false;
    }

    blockedClauseElimAll(lit);
    blockedClauseElimAll(~lit);

    var_elimed[lit.var()] = true;
    numElimed++;
    numMaxElimVars--;
    solver.setDecisionVar(lit.var(), false);

    return true;
}

void Subsumer::blockedClauseElimAll(const Lit lit)
{
    vec<ClauseSimp> toRemove(occur[lit.toInt()]);
    for (ClauseSimp *it = toRemove.getData(), *end = toRemove.getDataEnd(); it != end; it++) {
        #ifdef VERBOSE_DEBUG
        std::cout << "Next varelim because of block clause elim" << std::endl;
        #endif //VERBOSE_DEBUG
        unlinkClause(*it, lit.var());
        numblockedClauseRemoved++;
    }

    uint32_t removedNum = 0;
    vec<Watched>& ws = solver.watches[(~lit).toInt()];
    vec<Watched>::iterator i = ws.getData();
    vec<Watched>::iterator j = i;
    for (vec<Watched>::iterator end = ws.getDataEnd(); i != end; i++) {
        if (!i->isNonLearntBinary()) {
            *j++ = *i;
            continue;
        }
        assert(!i->getLearnt());
        removeWBin(solver.watches[(~i->getOtherLit()).toInt()], lit, false);
        elimedOutVarBin[lit.var()].push_back(std::make_pair(lit, i->getOtherLit()));
        touchedVars.touch(i->getOtherLit(), false);
        removedNum++;
    }
    ws.shrink_(i-j);

    solver.clauses_literals -= removedNum*2;
    solver.numBins -= removedNum;
}

/**
@brief Checks if eliminated variables are unassigned

If there is a variable that has been assigned even though it's been eliminated
that means that there were clauses that contained that variable, and where some-
how inserted into the watchlists. That would be a grave bug, since that would
mean that not all clauses containing the eliminated variable were removed during
the running of this class.

@return TRUE if they are all unassigned
*/
bool Subsumer::checkElimedUnassigned() const
{
    uint32_t checkNumElimed = 0;
    for (uint32_t i = 0; i < var_elimed.size(); i++) {
        if (var_elimed[i]) {
            checkNumElimed++;
            assert(solver.assigns[i] == l_Undef);
            if (solver.assigns[i] != l_Undef) return false;
        }
    }
    assert(numElimed == checkNumElimed);

    return true;
}

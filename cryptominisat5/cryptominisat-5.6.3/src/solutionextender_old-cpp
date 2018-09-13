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

#include "solutionextender.h"
#include "varreplacer.h"
#include "occsimplifier.h"
#include "solver.h"
#include "completedetachreattacher.h"
using namespace CMSat;
using std::cout;
using std::endl;

SolutionExtender::SolutionExtender(
    Solver* _solver
    , const vector<lbool>& _solution
) :
    solver(_solver)
    , qhead (0)
    , assigns(_solution)
{
    solver->model.resize(nVarsOuter(), l_Undef);
    for (uint32_t var = 0; var < nVarsOuter(); var++) {
        solver->model[var] = value(var);
    }
    release_assert(solver->verify_model());
}

/**
@brief Extends a SAT solution to the full solution

variable elimination, variable replacement, sub-part solving, etc. all need to
be handled correctly to arrive at a solution that is a solution to ALL of the
original problem, not just of what remained of it at the end inside this class
(i.e. we need to combine things from the helper classes)
*/
void SolutionExtender::extend()
{
    if (solver->conf.verbosity >= 3) {
        cout << "c Extending solution" << endl;
    }

    assert(clausesToFree.empty());

    //First detach all long clauses
    CompleteDetachReatacher detachReattach(solver);
    detachReattach.detach_nonbins_nontris();

    //Make watches large enough to fit occur of all
    solver->watches.resize(nVarsOuter()*2);

    //Sanity check
    if (solver->occsimplifier) {
        solver->occsimplifier->check_elimed_vars_are_unassignedAndStats();
    }

    //Adding binary clauses representing equivalent literals
    if (solver->conf.verbosity >= 3) {
        cout << "c Adding equivalent literals" << endl;
    }
    solver->varReplacer->extend_model(this);

    if (solver->conf.verbosity >= 3) {
        cout << "c Picking braches and propagating" << endl;
    }

    //Pick branches as long as we can
    for (uint32_t var = 0; var < nVarsOuter(); var++) {
        if (value(var) == l_Undef
            //Don't pick replaced variables
            && solver->varData[var].removed != Removed::replaced
        ) {
            Lit toEnqueue = Lit(var, false);
            #ifdef VERBOSE_DEBUG_RECONSTRUCT
            cout << "c Picking lit for reconstruction: " << toEnqueue << endl;
            #endif
            enqueue(toEnqueue);

            const bool OK = propagate();
            if (!OK) {
                cout
                << "Error while picking lit " << toEnqueue
                << " and propagating after solution reconstruction"
                << endl;
                assert(false);

                std::exit(-1);
            }
        }
    }

    if (solver->conf.verbosity >= 3) {
        cout << "c Adding blocked clauses" << endl;
    }
    if (solver->occsimplifier) {
        solver->occsimplifier->extend_model(this);
    }

    //Copy&check model
    solver->model.resize(nVarsOuter(), l_Undef);
    for (uint32_t var = 0; var < nVarsOuter(); var++) {
        solver->model[var] = value(var);
    }

    release_assert(solver->verify_model());

    //free clauses
    for (vector<ClOffset>::iterator
        it = clausesToFree.begin(), end = clausesToFree.end()
        ; it != end
        ; ++it
    ) {
        solver->cl_alloc.clauseFree(*it);
    }
    clausesToFree.clear();

    //Reset watch size to smaller one
    solver->watches.resize(solver->nVars()*2);

    //Remove occur, go back to 0, and
    detachReattach.detach_nonbins_nontris();
    solver->cancelUntil(0);
    detachReattach.reattachLongs();
}

bool SolutionExtender::satisfiedNorm(const vector<Lit>& lits) const
{
    for (vector<Lit>::const_iterator
        it = lits.begin(), end = lits.end()
        ; it != end
        ; ++it
    ) {
        if (value(*it) == l_True)
            return true;
    }

    return false;
}

bool SolutionExtender::satisfiedXor(const vector<Lit>& lits, const bool rhs) const
{
    bool val = false;
    uint32_t undef = 0;
    for (vector<Lit>::const_iterator it = lits.begin(), end = lits.end(); it != end; ++it) {
        assert(it->unsign() == *it);
        if (value(it->var()) == l_True) val ^= true;
        if (value(it->var()) == l_Undef) undef++;
    }
    return (undef > 0 || val == rhs);
}

bool SolutionExtender::addClause(
    const vector< Lit >& givenLits
    , const Lit blockedOn
) {
    tmpLits = givenLits;

    //Remove lits set at 0-level or return TRUE if any is set to TRUE at 0-level
    vector<Lit>::iterator i = tmpLits.begin();
    vector<Lit>::iterator j = i;
    for (vector<Lit>::iterator end = tmpLits.end(); i != end; i++) {
        if (value(*i) == l_True && solver->varData[i->var()].level == 0) {
            return true;
        }

        if (value(*i) == l_False && solver->varData[i->var()].level == 0) {
            continue;
        }

        *j++ = *i;
    }
    tmpLits.resize(tmpLits.size()-(i-j));

    #ifdef VERBOSE_DEBUG_RECONSTRUCT
    cout << "c Adding extend clause: " << tmpLits << " blocked on: " << blockedOn << endl;
    #endif

    //Empty clause, oops!
    if (tmpLits.empty())
        return false;

    //Create new clause, and add it
    Clause* cl = solver->cl_alloc.Clause_new(
        tmpLits //the literals
        , 0 //the time it was created -- useless, ignoring
    );
    ClOffset offset = solver->cl_alloc.get_offset(cl);
    clausesToFree.push_back(offset);
    for (vector<Lit>::const_iterator
        it = tmpLits.begin(), end = tmpLits.end()
        ; it != end
        ; ++it
    ) {
        //Special used of blocked Lit -- for blocking, but not in the same
        //sense as the original
        solver->watches[it->toInt()].push(Watched(offset, blockedOn));
    }

    propagateCl(cl, blockedOn);
    if (!propagate()) {
        assert(false);
        return false;
    }

    return true;
}

inline bool SolutionExtender::prop_bin_cl(
    Watched*& i
    , const Lit p
) {
    const lbool val = value(i->lit2());
    if (val == l_Undef) {
        #ifdef VERBOSE_DEBUG_RECONSTRUCT
        cout
        << "c Due to cl "
        << ~p << ", " << i->lit2()
        << " propagate enqueueing "
        << i->lit2() << endl;
        #endif
        enqueue(i->lit2());
    } else if (val == l_False){
        return false;
    }

    return true;
}

bool SolutionExtender::propagate()
{
    bool ret = true;
    while(qhead < trail.size()) {
        const Lit p = trail[qhead++];
        watch_subarray_const ws = solver->watches[~p];
        for(const Watched*
            it = ws.begin(), end = ws.end()
            ; it != end
            ; ++it
        ) {
            if (it->isBin() && !it->red()) {
                bool thisret = prop_bin_cl(it, p);
                ret &= thisret;
                if (!thisret) {
                    cout
                    << "Problem with implicit binary clause: "
                    << ~p
                    << ", " << it->lit2()
                    << endl;
                }

                continue;
            }

            if (it->isClause()) {
                ClOffset offset = it->get_offset();
                const Clause* cl = solver->cl_alloc.ptr(offset);
                const Lit blockedOn = it->getBlockedLit();
                const bool thisRet = propagateCl(cl, blockedOn);
                if (!thisRet) {
                    cout << "Problem with clause: " << (*it) << endl;
                }
                ret &= thisRet;
            }
        }
    }

    return ret;
}

bool SolutionExtender::propagateCl(
    const Clause* cl
    , const Lit blockedOn
) {
    size_t numUndef = 0;
    Lit lastUndef = lit_Undef;
    for (const Lit
        *it = cl->begin(), *end = cl->end()
        ; it != end
        ; ++it
    ) {
        if (value(*it) == l_True) return true;
        if (value(*it) == l_False) continue;

        assert(value(*it) == l_Undef);
        numUndef++;

        //Doesn't propagate anything
        if (numUndef > 1)
            break;

        lastUndef = *it;
    }

    //Must set this one value
    if (numUndef == 1) {
        #ifdef VERBOSE_DEBUG_RECONSTRUCT
        cout << "c Due to cl " << *cl << " propagate enqueueing " << lastUndef << endl;
        #endif
        enqueue(lastUndef);
    }

    if (numUndef >= 1)
        return true;

    //Must flip
    #ifdef VERBOSE_DEBUG_RECONSTRUCT
    cout
    << "Flipping lit " << blockedOn
    << " due to clause " << *cl << endl;
    #endif
    assert(blockedOn != lit_Undef);

    if (solver->varData[blockedOn.var()].level == 0) {
        cout
        << "!! Flip 0-level var:"
        << solver->map_inter_to_outer(blockedOn.var()) + 1
        << endl;
    }

    assert(
        (solver->varData[blockedOn.var()].level != 0
            //|| solver->varData[blockedOn.var()].removed == Removed::decomposed
        )
        && "We cannot flip 0-level vars"
    );
    enqueue(blockedOn);
    replaceSet(blockedOn);
    return true;
}

void SolutionExtender::enqueue(const Lit lit)
{
    assigns[lit.var()] = boolToLBool(!lit.sign());
    trail.push_back(lit);
    #ifdef VERBOSE_DEBUG_RECONSTRUCT
    cout << "c Enqueueing lit " << lit << " during solution reconstruction" << endl;
    #endif
    solver->varData[lit.var()].level = std::numeric_limits< uint32_t >::max();
}

void SolutionExtender::replaceSet(Lit toSet)
{
    //set forward equivalent
    if (solver->varReplacer->isReplaced(toSet)) {
        assert(false && "Cannot use isReplaced from outside of solver!!!!");
        toSet = solver->varReplacer->get_lit_replaced_with(toSet);
        enqueue(toSet);
    }
    replaceBackwardSet(toSet);

    #ifdef VERBOSE_DEBUG_RECONSTRUCT
    cout << "c recursive set(s) done." << endl;
    #endif
}

void SolutionExtender::replaceBackwardSet(const Lit toSet)
{
    //set backward equiv
    map<uint32_t, vector<uint32_t> >::const_iterator revTable = solver->varReplacer->getReverseTable().find(toSet.var());
    if (revTable != solver->varReplacer->getReverseTable().end()) {
        const vector<uint32_t>& toGoThrough = revTable->second;
        for (size_t i = 0; i < toGoThrough.size(); i++) {
            //Get sign of replacement
            const Lit lit = Lit(toGoThrough[i], false);
            Lit tmp = solver->varReplacer->get_lit_replaced_with(lit);

            //Set var
            enqueue(lit ^ tmp.sign() ^ toSet.sign());
        }
    }
}

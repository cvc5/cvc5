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

#ifndef __PROPENGINE_H__
#define __PROPENGINE_H__

#include <cstdio>
#include <string.h>
#include <stack>
#include <set>
#include <cmath>

//#define ANIMATE3D

#include "constants.h"
#include "propby.h"

#include "avgcalc.h"
#include "propby.h"
#include "heap.h"
#include "alg.h"
#include "clause.h"
#include "boundedqueue.h"
#include "cnf.h"
#include "watchalgos.h"

namespace CMSat {

using std::set;
class Solver;
class SQLStats;

//#define VERBOSE_DEBUG_FULLPROP
//#define DEBUG_STAMPING
//#define VERBOSE_DEBUG

#ifdef VERBOSE_DEBUG
#define VERBOSE_DEBUG_FULLPROP
#define ENQUEUE_DEBUG
#define DEBUG_ENQUEUE_LEVEL0
#endif

class Solver;
class ClauseAllocator;
class Gaussian;

enum PropResult {
    PROP_FAIL = 0
    , PROP_NOTHING = 1
    , PROP_SOMETHING = 2
    , PROP_TODO = 3
};

/**
@brief The propagating and conflict generation class

Handles watchlists, conflict analysis, propagation, variable settings, etc.
*/
class PropEngine: public CNF
{
public:

    // Constructor/Destructor:
    //
    PropEngine(
        const SolverConf* _conf
        , std::atomic<bool>* _must_interrupt_inter
    );
    ~PropEngine();

    // Read state:
    //
    uint32_t nAssigns   () const;         ///<The current number of assigned literals.

    //Get state
    uint32_t    decisionLevel() const;      ///<Returns current decision level
    size_t      getTrailSize() const; //number of variables set at decision level 0
    size_t trail_size() const {
        return trail.size();
    }
    Lit trail_at(size_t at) const {
        return trail[at];
    }
    bool propagate_occur();
    PropStats propStats;
    template<bool update_bogoprops = true>
    void enqueue(const Lit p, const PropBy from = PropBy());
    void new_decision_level();
    vector<double> var_act_vsids;
    vector<double> var_act_maple;

protected:
    int64_t simpDB_props = 0;
    void new_var(const bool bva, const uint32_t orig_outer) override;
    void new_vars(const size_t n) override;
    void save_on_var_memory();
    template<class T> uint32_t calc_glue(const T& ps);

    //For state saving
    void save_state(SimpleOutFile& f) const;
    void load_state(SimpleInFile& f);

    //Stats for conflicts
    ConflCausedBy lastConflictCausedBy;

    // Solver state:
    //
    vector<Lit>         trail;            ///< Assignment stack; stores all assigments made in the order they were made.
    vector<uint32_t>    trail_lim;        ///< Separator indices for different decision levels in 'trail'.
    uint32_t            qhead;            ///< Head of queue (as index into the trail)
    Lit                 failBinLit;       ///< Used to store which watches[lit] we were looking through when conflict occured


    struct VarOrderLt { ///Order variables according to their activities
        const vector<double>&  activities;
        bool operator () (const uint32_t x, const uint32_t y) const
        {
            return activities[x] > activities[y];
        }

        explicit VarOrderLt(const vector<double>& _activities) :
            activities(_activities)
        {}
    };

    ///activity-ordered heap of decision variables.
    ///NOT VALID WHILE SIMPLIFYING
    Heap<VarOrderLt> order_heap_vsids;
    Heap<VarOrderLt> order_heap_maple;

    friend class EGaussian;

    template<bool update_bogoprops>
    PropBy propagate_any_order();
    PropBy propagate_any_order_fast();
    PropBy propagate_strict_order();
    /*template<bool update_bogoprops>
    bool handle_xor_cl(
        Watched*& i
        , Watched*& &j
        , const Lit p
        , PropBy& confl
    );*/
    PropBy propagateIrredBin();  ///<For debug purposes, to test binary clause removal
    PropResult prop_normal_helper(
        Clause& c
        , ClOffset offset
        , Watched*& j
        , const Lit p
    );
    PropResult handle_normal_prop_fail(Clause& c, ClOffset offset, PropBy& confl);

    /////////////////
    // Operations on clauses:
    /////////////////
    void attachClause(
        const Clause& c
        , const bool checkAttach = true
    );

    void detach_bin_clause(
        Lit lit1
        , Lit lit2
        , bool red
        , bool allow_empty_watch = false
        , bool allow_change_order = false
    ) {
        if (!allow_change_order) {
            if (!(allow_empty_watch && watches[lit1].empty())) {
                removeWBin(watches, lit1, lit2, red);
            }
            if (!(allow_empty_watch && watches[lit2].empty())) {
                removeWBin(watches, lit2, lit1, red);
            }
        } else {
            if (!(allow_empty_watch && watches[lit1].empty())) {
                removeWBin_change_order(watches, lit1, lit2, red);
            }
            if (!(allow_empty_watch && watches[lit2].empty())) {
                removeWBin_change_order(watches, lit2, lit1, red);
            }
        }
    }
    void attach_bin_clause(
        const Lit lit1
        , const Lit lit2
        , const bool red
        , const bool checkUnassignedFirst = true
    );
    void detach_modified_clause(
        const Lit lit1
        , const Lit lit2
        , const Clause* address
    );

    // Debug & etc:
    void     print_all_clauses();
    void     printWatchList(const Lit lit) const;
    bool     satisfied(const BinaryClause& bin);
    void     print_trail();

    //Var selection, activity, etc.
    void updateVars(
        const vector<uint32_t>& outerToInter
        , const vector<uint32_t>& interToOuter
        , const vector<uint32_t>& interToOuter2
    );
    void updateWatch(watch_subarray ws, const vector<uint32_t>& outerToInter);

    size_t mem_used() const
    {
        size_t mem = 0;
        mem += CNF::mem_used();
        mem += trail.capacity()*sizeof(Lit);
        mem += trail_lim.capacity()*sizeof(uint32_t);
        mem += toClear.capacity()*sizeof(Lit);
        return mem;
    }

private:
    bool propagate_binary_clause_occur(const Watched& ws);
    bool propagate_long_clause_occur(const ClOffset offset);
    template<bool update_bogoprops = true>
    bool prop_bin_cl(
        const Watched* i
        , const Lit p
        , PropBy& confl
    ); ///<Propagate 2-long clause
    template<bool update_bogoprops>
    bool prop_long_cl_any_order(
        Watched* i
        , Watched*& j
        , const Lit p
        , PropBy& confl
    );
};


///////////////////////////////////////
// Implementation of inline methods:

inline void PropEngine::new_decision_level()
{
    trail_lim.push_back(trail.size());
    #ifdef VERBOSE_DEBUG
    cout << "New decision level: " << trail_lim.size() << endl;
    #endif
}

inline uint32_t PropEngine::decisionLevel() const
{
    return trail_lim.size();
}

inline uint32_t PropEngine::nAssigns() const
{
    return trail.size();
}

inline size_t PropEngine::getTrailSize() const
{
    if (decisionLevel() == 0) {
        return trail.size();
    } else {
        return trail_lim[0];
    }
}

inline bool PropEngine::satisfied(const BinaryClause& bin)
{
    return ((value(bin.getLit1()) == l_True)
            || (value(bin.getLit2()) == l_True));
}

template<class T> inline
uint32_t PropEngine::calc_glue(const T& ps)
{
    MYFLAG++;
    uint32_t nblevels = 0;
    for (Lit lit: ps) {
        int l = varData[lit.var()].level;
        if (l != 0 && permDiff[l] != MYFLAG) {
            permDiff[l] = MYFLAG;
            nblevels++;
            if (nblevels >= 50) {
                return nblevels;
            }
        }
    }
    return nblevels;
}

inline PropResult PropEngine::prop_normal_helper(
    Clause& c
    , ClOffset offset
    , Watched*& j
    , const Lit p
) {
    #ifdef STATS_NEEDED
    c.stats.clause_looked_at++;
    #endif

    // Make sure the false literal is data[1]:
    if (c[0] == ~p) {
        std::swap(c[0], c[1]);
    }

    assert(c[1] == ~p);

    // If 0th watch is true, then clause is already satisfied.
    if (value(c[0]) == l_True) {
        *j = Watched(offset, c[0]);
        j++;
        return PROP_NOTHING;
    }

    // Look for new watch:
    for (Lit *k = c.begin() + 2, *end2 = c.end()
        ; k != end2
        ; k++
    ) {
        //Literal is either unset or satisfied, attach to other watchlist
        if (value(*k) != l_False) {
            c[1] = *k;
            *k = ~p;
            watches[c[1]].push(Watched(offset, c[0]));
            return PROP_NOTHING;
        }
    }

    return PROP_TODO;
}


inline PropResult PropEngine::handle_normal_prop_fail(
    Clause&
    #ifdef STATS_NEEDED
    c
    #endif
    , ClOffset offset
    , PropBy& confl
) {
    confl = PropBy(offset);
    #ifdef VERBOSE_DEBUG_FULLPROP
    cout << "Conflict from ";
    for(size_t i = 0; i < c.size(); i++) {
        cout  << c[i] << " , ";
    }
    cout << endl;
    #endif //VERBOSE_DEBUG_FULLPROP

    //Update stats
    #ifdef STATS_NEEDED
    c.stats.conflicts_made++;
    c.stats.sum_of_branch_depth_conflict += decisionLevel() + 1;
    if (c.red())
        lastConflictCausedBy = ConflCausedBy::longred;
    else
        lastConflictCausedBy = ConflCausedBy::longirred;
    #endif

    qhead = trail.size();
    return PROP_FAIL;
}

template<bool update_bogoprops>
void PropEngine::enqueue(const Lit p, const PropBy from)
{
    #ifdef DEBUG_ENQUEUE_LEVEL0
    #ifndef VERBOSE_DEBUG
    if (decisionLevel() == 0)
    #endif //VERBOSE_DEBUG
    cout << "enqueue var " << p.var()+1
    << " to val " << !p.sign()
    << " level: " << decisionLevel()
    << " sublevel: " << trail.size()
    << " by: " << from << endl;
    #endif //DEBUG_ENQUEUE_LEVEL0

    #ifdef ENQUEUE_DEBUG
    assert(trail.size() <= nVarsOuter());
    assert(varData[p.var()].removed == Removed::none);
    #endif

    const uint32_t v = p.var();
    assert(value(v) == l_Undef);
    if (!watches[~p].empty()) {
        watches.prefetch((~p).toInt());
    }

    if (!update_bogoprops && !VSIDS) {
        varData[v].last_picked = sumConflicts;
        varData[v].conflicted = 0;

        assert(sumConflicts >= varData[v].cancelled);
        uint32_t age = sumConflicts - varData[v].cancelled;
        if (age > 0) {
            double decay = std::pow(0.95, age);
            var_act_maple[v] *= decay;
            if (order_heap_maple.inHeap(v))
                order_heap_maple.increase(v);
        }
    }

    const bool sign = p.sign();
    assigns[v] = boolToLBool(!sign);
    varData[v].reason = from;
    varData[v].level = decisionLevel();
    if (!update_bogoprops) {
        varData[v].polarity = !sign;
        #ifdef STATS_NEEDED
        if (sign) {
            propStats.varSetNeg++;
        } else {
            propStats.varSetPos++;
        }
        #endif
    }
    trail.push_back(p);

    if (update_bogoprops) {
        propStats.bogoProps += 1;
    }

    #ifdef ANIMATE3D
    std::cerr << "s " << v << " " << p.sign() << endl;
    #endif
}

inline void PropEngine::attach_bin_clause(
    const Lit lit1
    , const Lit lit2
    , const bool red
    , const bool
    #ifdef DEBUG_ATTACH
    checkUnassignedFirst
    #endif
) {
    #ifdef DEBUG_ATTACH
    assert(lit1.var() != lit2.var());
    if (checkUnassignedFirst) {
        assert(value(lit1.var()) == l_Undef);
        assert(value(lit2) == l_Undef || value(lit2) == l_False);
    }

    assert(varData[lit1.var()].removed == Removed::none);
    assert(varData[lit2.var()].removed == Removed::none);
    #endif //DEBUG_ATTACH

    watches[lit1].push(Watched(lit2, red));
    watches[lit2].push(Watched(lit1, red));
}

} //end namespace

#endif //__PROPENGINE_H__

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

#ifndef __SUBSUMESTRENGTHEN_H__
#define __SUBSUMESTRENGTHEN_H__

#include "cloffset.h"
#include "cryptominisat5/solvertypesmini.h"
#include "clabstraction.h"
#include "clause.h"
#include <vector>
using std::vector;

namespace CMSat {

class OccSimplifier;
class GateFinder;
class Solver;

class SubsumeStrengthen
{
public:
    SubsumeStrengthen(OccSimplifier* simplifier, Solver* solver);
    size_t mem_used() const;

    void backw_sub_long_with_long();
    bool backw_str_long_with_long();
    bool backw_sub_str_long_with_bins();

    //Called from simplifier at resolvent-adding of var-elim
    uint32_t subsume_and_unlink_and_markirred(const ClOffset offset);
    uint32_t backw_sub_long_with_implicit(const vector<Lit>& lits);
    bool backw_sub_str_long_with_bins_watch(
        const Lit lit
        , const bool redundant_too = false
    );
    bool handle_added_long_cl(int64_t* limit, const bool main_run);

    struct Sub0Ret {
        ClauseStats stats;
        bool subsumedIrred = 0;
        uint32_t numSubsumed = 0;
    };

    struct Sub1Ret {
        Sub1Ret& operator+=(const Sub1Ret& other)
        {
            sub += other.sub;
            str += other.str;

            return *this;
        }

        size_t sub = 0;
        size_t str = 0;
        bool subsumedIrred = false;
    };

    Sub1Ret backw_sub_str_long_with_implicit(const vector<Lit>& lits);
    Sub1Ret strengthen_subsume_and_unlink_and_markirred(ClOffset offset);

    struct Stats
    {
        Stats& operator+=(const Stats& other);
        void print_short(const Solver* solver) const;
        void print() const;

        uint64_t subsumedBySub = 0;
        uint64_t subsumedByStr = 0;
        uint64_t litsRemStrengthen = 0;

        double subsumeTime = 0.0;
        double strengthenTime = 0.0;
    };

    void finishedRun();
    const Stats& get_stats() const;
    const Stats& getRunStats() const;

    template<class T>
    void find_subsumed(
        const ClOffset offset
        , const T& ps
        , const cl_abst_type abs
        , vector<ClOffset>& out_subsumed
        , const bool removeImplicit = false
    );

private:
    Stats globalstats;
    Stats runStats;

    OccSimplifier* simplifier;
    Solver* solver;

    //Called from simplifier at resolvent-adding of var-elim
    template<class T>
    Sub0Ret subsume_and_unlink(
        const ClOffset offset
        , const T& ps
        , const cl_abst_type abs
        , const bool removeImplicit = false
    );

    void randomise_clauses_order();
    void remove_literal(ClOffset c, const Lit toRemoveLit);

    template<class T>
    size_t find_smallest_watchlist_for_clause(const T& ps) const;

    template<class T>
    void findStrengthened(
        const ClOffset offset
        , const T& ps
        , const cl_abst_type abs
        , vector<ClOffset>& out_subsumed
        , vector<Lit>& out_lits
    );

    template<class T>
    void fillSubs(
        const ClOffset offset
        , const T& ps
        , cl_abst_type abs
        , vector<ClOffset>& out_subsumed
        , vector<Lit>& out_lits
        , const Lit lit
    );

    template<class T1, class T2>
    bool subset(const T1& A, const T2& B);

    template<class T1, class T2>
    Lit subset1(const T1& A, const T2& B);
    bool subsetAbst(const cl_abst_type A, const cl_abst_type B);

    vector<ClOffset> subs;
    vector<Lit> subsLits;
    vector<Lit> tmpLits;
    size_t tried_bin_tri = 0;
    uint64_t subsumedBin = 0;
    uint64_t strBin = 0;
};

inline const SubsumeStrengthen::Stats& SubsumeStrengthen::getRunStats() const
{
    return runStats;
}

inline const SubsumeStrengthen::Stats& SubsumeStrengthen::get_stats() const
{
    return globalstats;
}

} //end namespace

#endif //__SUBSUMESTRENGTHEN_H__

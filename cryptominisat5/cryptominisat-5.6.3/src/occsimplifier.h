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

#ifndef SIMPLIFIER_H
#define SIMPLIFIER_H


#include <map>
#include <vector>
#include <list>
#include <set>
#include <queue>
#include <map>
#include <iomanip>
#include <fstream>

#include "clause.h"
#include "solvertypes.h"
#include "heap.h"
#include "touchlist.h"
#include "varupdatehelper.h"
#include "watched.h"
#include "watcharray.h"
#include "simplefile.h"

namespace CMSat {

using std::vector;
using std::map;
using std::set;
using std::pair;
using std::priority_queue;

class ClauseCleaner;
class SolutionExtender;
class Solver;
class TopLevelGaussAbst;
class SubsumeStrengthen;
class BVA;

struct BlockedClauses {
    BlockedClauses()
    {}

    explicit BlockedClauses(size_t _start, size_t _end) :
        start(_start)
        , end(_end)
        , toRemove(false)
    {}

    void save_to_file(SimpleOutFile& f) const
    {
        f.put_uint32_t(toRemove);
        f.put_uint64_t(start);
        f.put_uint64_t(end);
    }

    void load_from_file(SimpleInFile& f)
    {
        toRemove = f.get_uint32_t();
        start = f.get_uint64_t();
        end = f.get_uint64_t();
    }

    const Lit& at(const uint64_t at, const vector<Lit>& blkcls) const
    {
        return blkcls[start+at];
    }

    Lit& at(const uint64_t at, vector<Lit>& blkcls)
    {
        return blkcls[start+at];
    }

    uint64_t size() const {
        return end-start;
    }

    uint64_t start;
    uint64_t end;
    bool toRemove = false;
};

struct BVEStats
{
    uint64_t numCalls = 0;
    double timeUsed = 0.0;

    int64_t numVarsElimed = 0;
    uint64_t varElimTimeOut = 0;
    uint64_t clauses_elimed_long = 0;
    uint64_t clauses_elimed_tri = 0;
    uint64_t clauses_elimed_bin = 0;
    uint64_t clauses_elimed_sumsize = 0;
    uint64_t longRedClRemThroughElim = 0;
    uint64_t binRedClRemThroughElim = 0;
    uint64_t numRedBinVarRemAdded = 0;
    uint64_t testedToElimVars = 0;
    uint64_t triedToElimVars = 0;
    uint64_t newClauses = 0;
    uint64_t subsumedByVE = 0;

    BVEStats& operator+=(const BVEStats& other);

    void print() const
    {
        //About elimination
        cout
        << "c [occ-bve]"
        << " elimed: " << numVarsElimed
        << endl;

        cout
        << "c [occ-bve]"
        << " cl-new: " << newClauses
        << " tried: " << triedToElimVars
        << " tested: " << testedToElimVars
        << endl;

        cout
        << "c [occ-bve]"
        << " subs: "  << subsumedByVE
        << " red-bin rem: " << binRedClRemThroughElim
        << " red-long rem: " << longRedClRemThroughElim
        << endl;
    }

    void print()
    {
        print_stats_line("c timeouted"
            , stats_line_percent(varElimTimeOut, numCalls)
            , "% called"
        );
        print_stats_line("c v-elimed"
            , numVarsElimed
            , "% vars"
        );

        /*cout << "c"
        << " v-elimed: " << numVarsElimed
        << " / " << origNumMaxElimVars
        << " / " << origNumFreeVars
        << endl;*/

        print_stats_line("c cl-new"
            , newClauses
        );

        print_stats_line("c tried to elim"
            , triedToElimVars
        );

        print_stats_line("c elim-bin-lt-cl"
            , binRedClRemThroughElim);

        print_stats_line("c elim-long-lt-cl"
            , longRedClRemThroughElim);

        print_stats_line("c lt-bin added due to v-elim"
            , numRedBinVarRemAdded);

        print_stats_line("c cl-elim-bin"
            , clauses_elimed_bin);

        print_stats_line("c cl-elim-tri"
            , clauses_elimed_tri);

        print_stats_line("c cl-elim-long"
            , clauses_elimed_long);

        print_stats_line("c cl-elim-avg-s",
            ((double)clauses_elimed_sumsize
            /(double)(clauses_elimed_bin + clauses_elimed_tri + clauses_elimed_long))
        );

        print_stats_line("c v-elim-sub"
            , subsumedByVE
        );
    }
    void clear() {
        BVEStats tmp;
        *this = tmp;
    }
};

/**
@brief Handles subsumption, self-subsuming resolution, variable elimination, and related algorithms
*/
class OccSimplifier
{
public:

    //Construct-destruct
    explicit OccSimplifier(Solver* solver);
    ~OccSimplifier();

    //Called from main
    bool setup();
    bool simplify(const bool _startup, const std::string schedule);
    void new_var(const uint32_t orig_outer);
    void new_vars(const size_t n);
    void save_on_var_memory();
    bool uneliminate(const uint32_t var);
    size_t mem_used() const;
    size_t mem_used_xor() const;
    size_t mem_used_bva() const;
    void print_gatefinder_stats() const;
    void dump_blocked_clauses(std::ostream* outfile) const;

    //UnElimination
    void print_blocked_clauses_reverse() const;
    void extend_model(SolutionExtender* extender);
    uint32_t get_num_elimed_vars() const
    {
        return bvestats_global.numVarsElimed;
    }

    struct Stats
    {
        void print(const size_t nVars) const;
        void print_short() const;
        Stats& operator+=(const Stats& other);
        void clear();
        double total_time() const;

        uint64_t numCalls = 0;

        //Time stats
        double linkInTime = 0;
        double blockTime = 0;
        double varElimTime = 0;
        double finalCleanupTime = 0;

        //General stat
        uint64_t zeroDepthAssings = 0;
    };

    BVEStats bvestats;
    BVEStats bvestats_global;

    const Stats& get_stats() const;
    const SubsumeStrengthen* getSubsumeStrengthen() const;
    void check_elimed_vars_are_unassigned() const;
    void check_clid_correct() const;
    bool getAnythingHasBeenBlocked() const;
    void freeXorMem();
    void sort_occurs_and_set_abst();
    void save_state(SimpleOutFile& f);
    void load_state(SimpleInFile& f);
    vector<ClOffset> added_long_cl;
    TouchListLit added_cl_to_var;
    vector<uint32_t> n_occurs;
    TouchListLit removed_cl_with_var;
    vector<std::pair<Lit, Lit> > added_bin_cl;
    vector<ClOffset> clauses;
    void check_elimed_vars_are_unassignedAndStats() const;
    void unlink_clause(ClOffset cc
        , bool drat = true
        , bool allow_empty_watch = false
        , bool only_set_is_removed = false
    );
    void free_clauses_to_free();
    void cleanBlockedClausesIfDirty();

private:
    friend class SubsumeStrengthen;
    SubsumeStrengthen* sub_str;
    friend class BVA;
    BVA* bva;
    bool startup = false;
    bool backward_sub_str();
    bool execute_simplifier_strategy(const string& strategy);

    //debug
    bool subsetReverse(const Clause& B) const;

    //Persistent data
    Solver*  solver;              ///<The solver this simplifier is connected to
    vector<uint16_t>& seen;
    vector<uint8_t>& seen2;
    vector<Lit>& toClear;
    vector<bool> indep_vars;

    //Temporaries
    vector<Lit>     dummy;       ///<Used by merge()

    //Limits
    uint64_t clause_lits_added;
    int64_t  strengthening_time_limit;              ///<Max. number self-subsuming resolution tries to do this run
    int64_t  subsumption_time_limit;              ///<Max. number backward-subsumption tries to do this run
    int64_t  norm_varelim_time_limit;
    int64_t  empty_varelim_time_limit;
    int64_t  varelim_num_limit;
    int64_t  varelim_sub_str_limit;
    int64_t* limit_to_decrease;

    //Start-up
    bool fill_occur();
    bool fill_occur_and_print_stats();
    void finishUp(size_t origTrailSize);
    struct LinkInData
    {
        LinkInData()
        {}

        LinkInData(uint64_t _cl_linked, uint64_t _cl_not_linked) :
            cl_linked(_cl_linked)
            , cl_not_linked(_cl_not_linked)
        {}

        LinkInData& combine(const LinkInData& other)
        {
            cl_linked += other.cl_linked;
            cl_not_linked += other.cl_not_linked;
            return *this;
        }

        uint64_t cl_linked = 0;
        uint64_t cl_not_linked = 0;
    };
    LinkInData link_in_data_irred;
    LinkInData link_in_data_red;
    uint64_t calc_mem_usage_of_occur(const vector<ClOffset>& toAdd) const;
    void     print_mem_usage_of_occur(uint64_t memUsage) const;
    void     print_linkin_data(const LinkInData link_in_data) const;
    bool     decide_occur_limit(bool irred, uint64_t memUsage);
    OccSimplifier::LinkInData link_in_clauses(
        const vector<ClOffset>& toAdd
        , bool alsoOccur
        , uint32_t max_size
        , int64_t link_in_lit_limit
    );
    void set_limits();

    //Finish-up
    void remove_by_drat_recently_blocked_clauses(size_t origBlockedSize);
    void add_back_to_solver();
    bool check_varelim_when_adding_back_cl(const Clause* cl) const;
    void remove_all_longs_from_watches();
    bool complete_clean_clause(Clause& ps);

    //Clause update
    lbool       clean_clause(ClOffset c);
    void        linkInClause(Clause& cl);
    bool        handleUpdatedClause(ClOffset c);
    uint32_t    sum_irred_cls_longs() const;
    uint32_t    sum_irred_cls_longs_lits() const;

    struct watch_sort_smallest_first {
        bool operator()(const Watched& first, const Watched& second)
        {
            //Anything but clause!
            if (first.isClause())
                return false;
            if (second.isClause())
                return true;

            //Both are bin
            return false;
        }
    };

    /////////////////////
    //Variable elimination
    uint32_t grow = 0; /// maximum grow rate for clauses
    vector<uint64_t> varElimComplexity;
    ///Order variables according to their complexity of elimination
    struct VarOrderLt {
        const vector<uint64_t>&  varElimComplexity;
        bool operator () (const uint64_t x, const uint64_t y) const
        {
            return varElimComplexity[x] < varElimComplexity[y];
        }

        explicit VarOrderLt(
            const vector<uint64_t>& _varElimComplexity
        ) :
            varElimComplexity(_varElimComplexity)
        {}
    };
    void        order_vars_for_elim();
    Heap<VarOrderLt> velim_order;
    void        rem_cls_from_watch_due_to_varelim(watch_subarray todo, const Lit lit);
    vector<Lit> tmp_rem_lits;
    vec<Watched> tmp_rem_cls_copy;
    void        add_clause_to_blck(const vector<Lit>& lits);
    void        set_var_as_eliminated(const uint32_t var, const Lit lit);
    bool        can_eliminate_var(const uint32_t var) const;
    bool        clear_vars_from_cls_that_have_been_set(size_t& last_trail);
    bool        deal_with_added_cl_to_var_lit(const Lit lit);
    bool        simulate_frw_sub_str_with_added_cl_to_var();


    TouchList   elim_calc_need_update;
    vector<ClOffset> cl_to_free_later;
    bool        maybe_eliminate(const uint32_t x);
    bool        deal_with_added_long_and_bin(const bool main);
    bool        prop_and_clean_long_and_impl_clauses();
    vector<Lit> tmp_bin_cl;
    void        create_dummy_blocked_clause(const Lit lit);
    int         test_elim_and_fill_resolvents(uint32_t var);
    void        mark_gate_in_poss_negs(Lit elim_lit, watch_subarray_const poss, watch_subarray_const negs);
    void        find_gate(Lit elim_lit, watch_subarray_const a, watch_subarray_const b);
    void        print_var_eliminate_stat(Lit lit) const;
    bool        add_varelim_resolvent(vector<Lit>& finalLits, const ClauseStats& stats, bool is_xor);
    void        update_varelim_complexity_heap();
    void        print_var_elim_complexity_stats(const uint32_t var) const;

    struct ResolventData {
        ResolventData()
        {}

        ResolventData(const ClauseStats& cls, const bool _is_xor) :
            stats(cls),
            is_xor(_is_xor)
        {}

        ClauseStats stats;
        bool is_xor;
    };

    struct Resolvents {
        uint32_t at = 0;
        vector<vector<Lit>> resolvents_lits;
        vector<ResolventData> resolvents_stats;
        void clear() {
            at = 0;
        }
        void add_resolvent(const vector<Lit>& res, const ClauseStats& stats, bool is_xor) {
            if (resolvents_lits.size() < at+1) {
                resolvents_lits.resize(at+1);
                resolvents_stats.resize(at+1);
            }

            resolvents_lits[at] = res;
            resolvents_stats[at] = ResolventData(stats, is_xor);
            at++;
        }
        vector<Lit>& back_lits() {
            assert(at > 0);
            return resolvents_lits[at-1];
        }
        const ClauseStats& back_stats() const {
            assert(at > 0);
            return resolvents_stats[at-1].stats;
        }
        bool back_xor() const {
            assert(at > 0);
            return resolvents_stats[at-1].is_xor;
        }
        void pop() {
            at--;
        }
        bool empty() const {
            return at == 0;
        }
        uint32_t size() const {
            return at;
        }
    };
    Resolvents resolvents;
    Clause* gate_varelim_clause;
    uint32_t calc_data_for_heuristic(const Lit lit);
    uint64_t time_spent_on_calc_otf_update;
    uint64_t num_otf_update_until_now;

    //for n_occur checking only
    uint32_t calc_occ_data(const Lit lit);
    void     check_n_occur();

    //For empty resolvents
    enum class ResolvCount{count, set, unset};
    bool check_empty_resolvent(const Lit lit);
    int check_empty_resolvent_action(
        const Lit lit
        , ResolvCount action
        , int otherSize
    );

    uint64_t heuristicCalcVarElimScore(const uint32_t var);
    bool resolve_clauses(
        const Watched ps
        , const Watched qs
        , const Lit noPosLit
    );
    void add_pos_lits_to_dummy_and_seen(
        const Watched ps
        , const Lit posLit
    );
    bool add_neg_lits_to_dummy_and_seen(
        const Watched qs
        , const Lit posLit
    );
    bool eliminate_vars();
    void eliminate_empty_resolvent_vars();

    /////////////////////
    //Helpers
    friend class TopLevelGaussAbst;
    //friend class GateFinder;
    TopLevelGaussAbst *topLevelGauss;
    //GateFinder *gateFinder;

    /////////////////////
    //Blocked clause elimination
    bool anythingHasBeenBlocked;
    vector<Lit> blkcls;
    vector<BlockedClauses> blockedClauses; ///<maps var(outer!!) to postion in blockedClauses
    vector<uint32_t> blk_var_to_cls;
    bool blockedMapBuilt;
    void buildBlockedMap();
    void cleanBlockedClauses();
    bool can_remove_blocked_clauses = false;

    //validity checking
    void sanityCheckElimedVars();
    void printOccur(const Lit lit) const;

    ///Stats from this run
    Stats runStats;

    ///Stats globally
    Stats globalStats;
};

inline const OccSimplifier::Stats& OccSimplifier::get_stats() const
{
    return globalStats;
}

inline bool OccSimplifier::getAnythingHasBeenBlocked() const
{
    return anythingHasBeenBlocked;
}

/*inline std::ostream& operator<<(std::ostream& os, const BlockedClauses& bl)
{
    os << bl.lits << " to remove: " << bl.toRemove;

    return os;
}*/

inline bool OccSimplifier::subsetReverse(const Clause& B) const
{
    for (uint32_t i = 0; i != B.size(); i++) {
        if (!seen[B[i].toInt()])
            return false;
    }
    return true;
}

inline const SubsumeStrengthen* OccSimplifier::getSubsumeStrengthen() const
{
    return sub_str;
}

} //end namespace

#endif //SIMPLIFIER_H

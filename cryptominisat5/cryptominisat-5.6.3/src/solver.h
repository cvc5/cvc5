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

#ifndef SOLVER_H
#define SOLVER_H

#include "constants.h"
#include <vector>
#include <fstream>
#include <iostream>
#include <utility>
#include <string>

#include "constants.h"
#include "solvertypes.h"
#include "implcache.h"
#include "propengine.h"
#include "searcher.h"
#include "clauseusagestats.h"
#include "solvefeatures.h"
#include "searchstats.h"
#ifdef CMS_TESTING_ENABLED
#include "gtest/gtest_prod.h"
#endif

namespace CMSat {

using std::vector;
using std::pair;
using std::string;

class VarReplacer;
class ClauseCleaner;
class Prober;
class OccSimplifier;
class SCCFinder;
class DistillerLong;
class DistillerLongWithImpl;
class StrImplWImplStamp;
class CalcDefPolars;
class SolutionExtender;
class ImplCache;
class CompFinder;
class CompHandler;
class SubsumeStrengthen;
class SubsumeImplicit;
class DataSync;
class SharedData;
class ReduceDB;
class InTree;

struct SolveStats
{
    uint64_t numSimplify = 0;
    uint32_t num_solve_calls = 0;
};

class Solver : public Searcher
{
    public:
        Solver(const SolverConf *_conf = NULL, std::atomic<bool>* _must_interrupt_inter = NULL);
        ~Solver() override;

        void add_sql_tag(const string& tagname, const string& tag);
        const vector<std::pair<string, string> >& get_sql_tags() const;
        void new_external_var();
        void new_external_vars(size_t n);
        bool add_clause_outer(const vector<Lit>& lits, bool red = false);
        bool add_xor_clause_outer(const vector<uint32_t>& vars, bool rhs);

        lbool solve_with_assumptions(const vector<Lit>* _assumptions, bool only_indep_solution);
        lbool simplify_with_assumptions(const vector<Lit>* _assumptions = NULL);
        void  set_shared_data(SharedData* shared_data);

        //Querying model
        lbool model_value (const Lit p) const;  ///<Found model value for lit
        lbool model_value (const uint32_t p) const;  ///<Found model value for var
        lbool full_model_value (const Lit p) const;  ///<Found model value for lit
        lbool full_model_value (const uint32_t p) const;  ///<Found model value for var
        const vector<lbool>& get_model() const;
        const vector<Lit>& get_final_conflict() const;
        vector<pair<Lit, Lit> > get_all_binary_xors() const;
        vector<Xor> get_recovered_xors(bool elongate);

        //get learnt clauses
        void start_getting_small_clauses(uint32_t max_len, uint32_t max_glue);
        bool get_next_small_clause(std::vector<Lit>& out);
        void end_getting_small_clauses();

        void open_file_and_dump_irred_clauses(string fname) const;
        void open_file_and_dump_red_clauses(string fname) const;

        static const char* get_version_tag();
        static const char* get_version_sha1();
        static const char* get_compilation_env();

        vector<Lit> get_zero_assigned_lits(const bool backnumber = true, bool only_nvars = false) const;
        void     print_stats(const double cpu_time) const;
        void     print_clause_stats() const;
        size_t get_num_free_vars() const;
        size_t get_num_nonfree_vars() const;
        const SolverConf& getConf() const;
        void setConf(const SolverConf& conf);
        const BinTriStats& getBinTriStats() const;
        size_t   get_num_long_irred_cls() const;
        size_t   get_num_long_red_cls() const;
        size_t get_num_vars_elimed() const;
        uint32_t num_active_vars() const;
        void print_mem_stats() const;
        uint64_t print_watch_mem_used(uint64_t totalMem) const;
        unsigned long get_sql_id() const;
        const SolveStats& get_solve_stats() const;
        const SearchStats& get_stats() const;
        void add_in_partial_solving_stats();
        void check_implicit_stats(const bool onlypairs = false) const;
        void check_stats(const bool allowFreed = false) const;


        //Checks
        void check_implicit_propagated() const;
        bool find_with_stamp_a_or_b(Lit a, Lit b) const;
        bool find_with_cache_a_or_b(Lit a, Lit b, int64_t* limit) const;
        bool find_with_watchlist_a_or_b(Lit a, Lit b, int64_t* limit) const;

        //Systems that are used to accompilsh the tasks
        ClauseCleaner*         clauseCleaner = NULL;
        VarReplacer*           varReplacer = NULL;
        SubsumeImplicit*       subsumeImplicit = NULL;
        DataSync*              datasync = NULL;
        ReduceDB*              reduceDB = NULL;
        Prober*                prober = NULL;
        InTree*                intree = NULL;
        OccSimplifier*         occsimplifier = NULL;
        DistillerLong*         distill_long_cls = NULL;
        DistillerLongWithImpl* dist_long_with_impl = NULL;
        StrImplWImplStamp* dist_impl_with_impl = NULL;
        CompHandler*           compHandler = NULL;

        SearchStats sumSearchStats;
        PropStats sumPropStats;

        bool prop_at_head() const;
        void set_decision_var(const uint32_t var);
        bool fully_enqueue_these(const vector<Lit>& toEnqueue);
        bool fully_enqueue_this(const Lit lit);
        void update_assumptions_after_varreplace();

        //State load/unload
        void save_state(const string& fname, const lbool status) const;
        lbool load_state(const string& fname);
        template<typename A>
        void parse_v_line(A* in, const size_t lineNum);
        lbool load_solution_from_file(const string& fname);

        uint64_t getNumLongClauses() const;
        bool addClause(const vector<Lit>& ps, const bool red = false);
        bool add_xor_clause_inter(
            const vector< Lit >& lits
            , bool rhs
            , bool attach
            , bool addDrat = true
        );
        void new_var(const bool bva = false, const uint32_t orig_outer = std::numeric_limits<uint32_t>::max()) override;
        void new_vars(const size_t n) override;
        void bva_changed();

        //Attaching-detaching clauses
        void attachClause(
            const Clause& c
            , const bool checkAttach = true
        );
        void attach_bin_clause(
            const Lit lit1
            , const Lit lit2
            , const bool red
            , const bool checkUnassignedFirst = true
        );
        void detach_bin_clause(
            Lit lit1
            , Lit lit2
            , bool red
            , bool allow_empty_watch = false
            , bool allow_change_order = false
        ) {
            if (red) {
                binTri.redBins--;
            } else {
                binTri.irredBins--;
            }

            PropEngine::detach_bin_clause(lit1, lit2, red, allow_empty_watch, allow_change_order);
        }
        void detachClause(const Clause& c, const bool removeDrat = true);
        void detachClause(const ClOffset offset, const bool removeDrat = true);
        void detach_modified_clause(
            const Lit lit1
            , const Lit lit2
            , const uint32_t origSize
            , const Clause* address
        );
        Clause* add_clause_int(
            const vector<Lit>& lits
            , const bool red = false
            , const ClauseStats stats = ClauseStats()
            , const bool attach = true
            , vector<Lit>* finalLits = NULL
            , bool addDrat = true
            , const Lit drat_first = lit_Undef
        );
        template<class T> vector<Lit> clause_outer_numbered(const T& cl) const;
        template<class T> vector<uint32_t> xor_outer_numbered(const T& cl) const;
        size_t mem_used() const;
        void dump_memory_stats_to_sql();
        void set_sqlite(string filename);
        //Not Private for testing (maybe could be called from outside)
        bool renumber_variables(bool must_renumber = true);
        SolveFeatures calculate_features();
        SolveFeatures last_solve_feature;

        uint32_t undefine(vector<uint32_t>& trail_lim_vars);
        vector<Lit> get_toplevel_units_internal(bool outer_numbering) const;

        #ifdef USE_GAUSS
        bool init_all_matrixes();
        #endif


        //if set to TRUE, a clause has been removed during add_clause_int
        //that contained "lit, ~lit". So "lit" must be set to a value
        //Contains _outer_ variables
        vector<bool> undef_must_set_vars;

        //Helper
        void renumber_xors_to_outside(const vector<Xor>& xors, vector<Xor>& xors_ret);

    private:
        friend class Prober;
        friend class ClauseDumper;
        #ifdef CMS_TESTING_ENABLED
        FRIEND_TEST(SearcherTest, pickpolar_auto_not_changed_by_simp);
        #endif

        lbool iterate_until_solved();
        uint64_t mem_used_vardata() const;
        void check_reconfigure();
        void reconfigure(int val);
        bool already_reconfigured = false;
        long calc_num_confl_to_do_this_iter(const size_t iteration_num) const;

        vector<Lit> finalCl_tmp;
        bool sort_and_clean_clause(vector<Lit>& ps, const vector<Lit>& origCl, const bool red);
        void set_up_sql_writer();
        vector<std::pair<string, string> > sql_tags;

        void check_config_parameters() const;
        void check_xor_cut_config_sanity() const;
        void handle_found_solution(const lbool status, const bool only_indep_solution);
        void add_every_combination_xor(const vector<Lit>& lits, bool attach, bool addDrat);
        void add_xor_clause_inter_cleaned_cut(const vector<Lit>& lits, bool attach, bool addDrat);
        unsigned num_bits_set(const size_t x, const unsigned max_size) const;
        void check_too_large_variable_number(const vector<Lit>& lits) const;
        void set_assumptions();

        lbool simplify_problem_outside();
        void move_to_outside_assumps(const vector<Lit>* assumps);
        vector<Lit> back_number_from_outside_to_outer_tmp;
        void back_number_from_outside_to_outer(const vector<Lit>& lits)
        {
            back_number_from_outside_to_outer_tmp.clear();
            for (const Lit lit: lits) {
                assert(lit.var() < nVarsOutside());
                back_number_from_outside_to_outer_tmp.push_back(map_to_with_bva(lit));
                assert(back_number_from_outside_to_outer_tmp.back().var() < nVarsOuter());
            }
        }
        void check_switchoff_limits_newvar(size_t n = 1);
        vector<Lit> outside_assumptions;

        //Stats printing
        void print_norm_stats(const double cpu_time) const;
        void print_min_stats(const double cpu_time) const;
        void print_full_restart_stat(const double cpu_time) const;

        lbool simplify_problem(const bool startup);
        bool execute_inprocess_strategy(const bool startup, const string& strategy);
        SolveStats solveStats;
        void check_minimization_effectiveness(lbool status);
        void check_recursive_minimization_effectiveness(const lbool status);
        void extend_solution(const bool only_indep_solution);
        void check_too_many_low_glues();
        bool adjusted_glue_cutoff_if_too_many = false;

        /////////////////////////////
        // Temporary datastructs -- must be cleared before use
        mutable std::vector<Lit> tmpCl;
        mutable std::vector<uint32_t> tmpXor;


        //learnt clause querying
        uint32_t learnt_clause_query_max_len = std::numeric_limits<uint32_t>::max();
        uint32_t learnt_clause_query_max_glue = std::numeric_limits<uint32_t>::max();
        uint32_t learnt_clause_query_at = std::numeric_limits<uint32_t>::max();
        uint32_t learnt_clause_query_watched_at = std::numeric_limits<uint32_t>::max();
        uint32_t learnt_clause_query_watched_at_sub = std::numeric_limits<uint32_t>::max();
        vector<uint32_t> learnt_clause_query_outer_to_without_bva_map;
        bool all_vars_outside(const vector<Lit>& cl) const;
        void learnt_clausee_query_map_without_bva(vector<Lit>& cl);

        /////////////////////////////
        //Renumberer
        double calc_renumber_saving();
        void free_unused_watches();
        void save_on_var_memory(uint32_t newNumVars);
        void unSaveVarMem();
        size_t calculate_interToOuter_and_outerToInter(
            vector<uint32_t>& outerToInter
            , vector<uint32_t>& interToOuter
        );
        void renumber_clauses(const vector<uint32_t>& outerToInter);
        void test_renumbering() const;
        bool clean_xor_clauses_from_duplicate_and_set_vars();

        //Value Unsetter
        struct FindUndef {
            //If set to TRUE, then that clause already has only 1 lit that is true,
            //so it can be skipped during updateFixNeed()
            vector<char> dontLookAtClause;

            vector<uint32_t> satisfies;
            vector<unsigned char> can_be_unset;
            vector<uint32_t>* trail_lim_vars;
            int64_t can_be_unsetSum;
            bool must_fix_at_least_one_var;
            uint32_t num_fixed;
            bool verbose = false;
        };
        FindUndef* undef = NULL;
        bool undef_must_fix_var();
        void undef_fill_potentials();
        void undef_unset_potentials();
        template<class C> bool undef_clause_surely_satisfied(const C c);



        /////////////////////////////
        // SAT solution verification
        bool verify_model() const;
        bool verify_model_implicit_clauses() const;
        bool verify_model_long_clauses(const vector<ClOffset>& cs) const;


        /////////////////////
        // Data
        size_t               zeroLevAssignsByCNF = 0;

        /////////////////////
        // Clauses
        bool addClauseHelper(vector<Lit>& ps);

        /////////////////
        // Debug

        void print_watch_list(watch_subarray_const ws, const Lit lit) const;
        void print_clause_size_distrib();
        void print_prop_confl_stats(
            std::string name
            , const vector<ClauseUsageStats>& stats
        ) const;
        void check_model_for_assumptions() const;
};

inline void Solver::set_decision_var(const uint32_t var)
{
    insert_var_order_all(var);
}

inline uint64_t Solver::getNumLongClauses() const
{
    return longIrredCls.size() + longRedCls.size();
}

inline const SearchStats& Solver::get_stats() const
{
    return sumSearchStats;
}

inline const SolveStats& Solver::get_solve_stats() const
{
    return solveStats;
}

inline size_t Solver::get_num_long_irred_cls() const
{
    return longIrredCls.size();
}

inline size_t Solver::get_num_long_red_cls() const
{
    return longRedCls.size();
}

inline const SolverConf& Solver::getConf() const
{
    return conf;
}

inline const vector<std::pair<string, string> >& Solver::get_sql_tags() const
{
    return sql_tags;
}

inline const BinTriStats& Solver::getBinTriStats() const
{
    return binTri;
}

template<class T>
inline vector<Lit> Solver::clause_outer_numbered(const T& cl) const
{
    tmpCl.clear();
    for(size_t i = 0; i < cl.size(); i++) {
        tmpCl.push_back(map_inter_to_outer(cl[i]));
    }

    return tmpCl;
}

template<class T>
inline vector<uint32_t> Solver::xor_outer_numbered(const T& cl) const
{
    tmpXor.clear();
    for(size_t i = 0; i < cl.size(); i++) {
        tmpXor.push_back(map_inter_to_outer(cl[i]));
    }

    return tmpXor;
}

inline void Solver::move_to_outside_assumps(const vector<Lit>* assumps)
{
    outside_assumptions.clear();
    if (assumps) {
        for(const Lit lit: *assumps) {
            if (lit.var() >= nVarsOutside()) {
                std::cerr << "ERROR: Assumption variable " << (lit.var()+1)
                << " is too large, you never"
                << " inserted that variable into the solver. Exiting."
                << endl;
                exit(-1);
            }
            outside_assumptions.push_back(lit);
        }
    }
}

inline lbool Solver::simplify_with_assumptions(
    const vector<Lit>* _assumptions
) {
    move_to_outside_assumps(_assumptions);
    return simplify_problem_outside();
}

inline bool Solver::find_with_stamp_a_or_b(Lit a, const Lit b) const
{
    //start STAMP of A < start STAMP of B
    //end STAMP of A > start STAMP of B
    //means: ~A V B is inside
    //so, invert A
    a = ~a;

    const uint64_t start_inv_other = solver->stamp.tstamp[(a).toInt()].start[STAMP_IRRED];
    const uint64_t start_eqLit = solver->stamp.tstamp[b.toInt()].end[STAMP_IRRED];
    if (start_inv_other < start_eqLit) {
        const uint64_t end_inv_other = solver->stamp.tstamp[(a).toInt()].end[STAMP_IRRED];
        const uint64_t end_eqLit = solver->stamp.tstamp[b.toInt()].end[STAMP_IRRED];
        if (end_inv_other > end_eqLit) {
            return true;
        }
    }

    return false;
}

inline bool Solver::find_with_cache_a_or_b(Lit a, Lit b, int64_t* limit) const
{
    const vector<LitExtra>& cache = solver->implCache[a].lits;
    *limit -= cache.size();
    for (LitExtra cacheLit: cache) {
        if (cacheLit.getOnlyIrredBin()
            && cacheLit.getLit() == b
        ) {
            return true;
        }
    }

    std::swap(a,b);

    const vector<LitExtra>& cache2 = solver->implCache[a].lits;
    *limit -= cache2.size();
    for (LitExtra cacheLit: cache) {
        if (cacheLit.getOnlyIrredBin()
            && cacheLit.getLit() == b
        ) {
            return true;
        }
    }

    return false;
}

inline bool Solver::find_with_watchlist_a_or_b(Lit a, Lit b, int64_t* limit) const
{
    if (watches[a].size() > watches[b].size()) {
        std::swap(a,b);
    }

    watch_subarray_const ws = watches[a];
    *limit -= ws.size();
    for (const Watched w: ws) {
        if (!w.isBin())
            continue;

        if (!w.red()
            && w.lit2() == b
        ) {
            return true;
        }
    }

    return false;
}

inline const vector<lbool>& Solver::get_model() const
{
    return model;
}

inline const vector<Lit>& Solver::get_final_conflict() const
{
    return conflict;
}

inline void Solver::setConf(const SolverConf& _conf)
{
    conf = _conf;
}

inline bool Solver::prop_at_head() const
{
    return qhead == trail.size()
//     #ifdef USE_GAUSS
//     && gqhead == trail.size()
//     #endif
    ;
}

inline lbool Solver::model_value (const Lit p) const
{
    if (model[p.var()] == l_Undef)
        return l_Undef;

    return model[p.var()] ^ p.sign();
}

inline lbool Solver::model_value (const uint32_t p) const
{
    return model[p];
}

inline lbool Solver::full_model_value (const Lit p) const
{
    return full_model[p.var()] ^ p.sign();
}

inline lbool Solver::full_model_value  (const uint32_t p) const
{
    return full_model[p];
}

} //end namespace

#endif //SOLVER_H

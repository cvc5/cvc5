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

#ifndef SOLVERCONF_H
#define SOLVERCONF_H

#include <string>
#include <vector>
#include <cstdlib>
#include <cassert>
#include "constants.h"
#include "cryptominisat5/solvertypesmini.h"

using std::string;

namespace CMSat {

enum class ClauseClean {
    glue = 0
    , activity = 1
};

inline unsigned clean_to_int(ClauseClean t)
{
    switch(t)
    {
        case ClauseClean::glue:
            return 0;

        case ClauseClean::activity:
            return 1;
    }

    assert(false);
}

enum class PolarityMode {
    polarmode_pos
    , polarmode_neg
    , polarmode_rnd
    , polarmode_automatic
};

enum class Restart {
    glue
    , geom
    , glue_geom
    , luby
    , never
};

inline std::string getNameOfRestartType(Restart rest_type)
{
    switch(rest_type) {
        case Restart::glue :
            return "glue";

        case Restart::geom:
            return "geometric";

        case Restart::glue_geom:
            return "regularly switch between glue and geometric";

        case Restart::luby:
            return "luby";

        case Restart::never:
            return "never";

        default:
            assert(false && "Unknown clause cleaning type?");
    };
}

inline std::string getNameOfCleanType(ClauseClean clauseCleaningType)
{
    switch(clauseCleaningType) {
        case ClauseClean::glue :
            return "glue";

        case ClauseClean::activity:
            return "activity";

        default:
            assert(false && "Unknown clause cleaning type?");
            std::exit(-1);
    };
}

class GaussConf
{
    public:

    GaussConf() :
        decision_until(700)
        , autodisable(true)
        , max_matrix_rows(5000)
        , min_matrix_rows(2)
        , max_num_matrixes(5)
    {
    }

    uint32_t decision_until; //do Gauss until this level
    bool autodisable;
    uint32_t max_matrix_rows; //The maximum matrix size -- no. of rows
    uint32_t min_matrix_rows; //The minimum matrix size -- no. of rows
    uint32_t max_num_matrixes; //Maximum number of matrixes

    //Matrix extraction config
    bool doMatrixFind = true;
    uint32_t min_gauss_xor_clauses = 2;
    uint32_t max_gauss_xor_clauses = 500000;
};

class DLL_PUBLIC SolverConf
{
    public:
        SolverConf();
        std::string print_times(
            const double time_used
            , const bool time_out
            , const double time_remain
        ) const;
        std::string print_times(
            const double time_used
            , const bool time_out
        ) const;
        std::string print_times(
            const double time_used
        ) const;

        //Variable activities
        double  var_inc_vsids_start;
        double  var_decay_vsids_start;
        double  var_decay_vsids_max;
        double random_var_freq;
        PolarityMode polarity_mode;

        //Clause cleaning

        //if non-zero, we reduce at every X conflicts.
        //Reduced according to whether it's been used recently
        //Otherwise, we *never* reduce
        unsigned every_lev1_reduce;

        //if non-zero, we reduce at every X conflicts.
        //Otherwise we geometrically keep around max_temp_lev2_learnt_clauses*(inc**N)
        unsigned every_lev2_reduce;

        uint32_t must_touch_lev1_within;
        unsigned  max_temp_lev2_learnt_clauses;
        double    inc_max_temp_lev2_red_cls;

        unsigned protect_cl_if_improved_glue_below_this_glue_for_one_turn;
        unsigned glue_put_lev0_if_below_or_eq;
        unsigned glue_put_lev1_if_below_or_eq;
        double    ratio_keep_clauses[2]; ///< Remove this ratio of clauses at every database reduction round

        double    clause_decay;

        //If too many (in percentage) low glues after min_num_confl_adjust_glue_cutoff, adjust glue lower
        double   adjust_glue_if_too_many_low;
        uint64_t min_num_confl_adjust_glue_cutoff;

        int      guess_cl_effectiveness;

        //maple
        int      maple;
        unsigned modulo_maple_iter;
        bool     more_maple_bump_high_glue;

        //For restarting
        unsigned    restart_first;      ///<The initial restart limit.                                                                (default 100)
        double    restart_inc;        ///<The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
        Restart  restartType;   ///<If set, the solver will always choose the given restart strategy
        int       do_blocking_restart;
        unsigned blocking_restart_trail_hist_length;
        double   blocking_restart_multip;
        int      broken_glue_restart;

        double   local_glue_multiplier;
        unsigned  shortTermHistorySize; ///< Rolling avg. glue window size
        unsigned lower_bound_for_blocking_restart;
        double   ratio_glue_geom; //higher the number, the more glue will be done. 2 is 2x glue 1x geom
        int more_more_with_cache;
        int more_more_with_stamp;
        int doAlwaysFMinim;

        //Clause minimisation
        int doRecursiveMinim;
        int doMinimRedMore;  ///<Perform learnt clause minimisation using watchists' binary and tertiary clauses? ("strong minimization" in PrecoSat)
        int doMinimRedMoreMore;
        unsigned max_glue_more_minim;
        unsigned max_size_more_minim;
        unsigned more_red_minim_limit_cache;
        unsigned more_red_minim_limit_binary;
        unsigned max_num_lits_more_more_red_min;

        //Verbosity
        int  verbosity;  ///<Verbosity level. 0=silent, 1=some progress report, 2=lots of report, 3 = all report       (default 2) preferentiality is turned off (i.e. picked randomly between [0, all])
        int  doPrintGateDot; ///< Print DOT file of gates
        int  print_full_restart_stat;
        int  print_all_restarts;
        int  verbStats;
        int do_print_times; ///Print times during verbose output
        int print_restart_line_every_n_confl;

        //Limits
        double   maxTime;
        long max_confl;

        //Glues
        int       update_glues_on_analyze;

        //OTF stuff
        int       otfHyperbin;
        int       doOTFSubsume;
        int       doOTFSubsumeOnlyAtOrBelowGlue;

        //SQL
        bool      dump_individual_restarts_and_clauses;
        double    dump_individual_cldata_ratio;

        //Steps
        double orig_step_size = 0.40;
        double step_size_dec = 0.000001;
        double min_step_size = 0.06;

        //Var-elim
        int      doVarElim;          ///<Perform variable elimination
        uint64_t varelim_cutoff_too_many_clauses;
        int      do_empty_varelim;
        long long empty_varelim_time_limitM;
        long long varelim_time_limitM;
        long long varelim_sub_str_limit;
        double    varElimRatioPerIter;
        int      skip_some_bve_resolvents;
        int velim_resolvent_too_large; //-1 == no limit

        //Subs, str limits for simplifier
        long long subsumption_time_limitM;
        long long strengthening_time_limitM;
        long long aggressive_elim_time_limitM;

        //BVA
        int      do_bva;
        int min_bva_gain;
        unsigned bva_limit_per_call;
        int      bva_also_twolit_diff;
        long     bva_extra_lit_and_red_start;
        long long bva_time_limitM;

        //Probing
        int      doProbe;
        int      doIntreeProbe;
        unsigned long long   probe_bogoprops_time_limitM;
        unsigned long long   intree_time_limitM;
        unsigned long long intree_scc_varreplace_time_limitM;
        int      doBothProp;
        int      doTransRed;   ///<Should carry out transitive reduction
        int      doStamp;
        int      doCache;
        unsigned   cacheUpdateCutoff;
        unsigned   maxCacheSizeMB;
        unsigned long long otf_hyper_time_limitM;
        double  otf_hyper_ratio_limit;
        double single_probe_time_limit_perc;

        //XORs
        int      doFindXors;
        unsigned maxXorToFind;
        int      useCacheWhenFindingXors;
        int      doEchelonizeXOR;
        uint64_t maxXORMatrix;
        uint64_t xor_finder_time_limitM;
        int      allow_elim_xor_vars;
        unsigned xor_var_per_cut;

        //Var-replacement
        int doFindAndReplaceEqLits;
        int doExtendedSCC;
        int max_scc_depth;

        //Iterative Alo Scheduling
        int      simplify_at_startup; //simplify at 1st startup (only)
        int      simplify_at_every_startup; //always simplify at startup, not only at 1st startup
        int      do_simplify_problem;
        int      full_simplify_at_startup;
        int      never_stop_search;
        uint64_t num_conflicts_of_search;
        double   num_conflicts_of_search_inc;
        double   num_conflicts_of_search_inc_max;
        string   simplify_schedule_startup;
        string   simplify_schedule_nonstartup;
        string   simplify_schedule_preproc;

        //Simplification
        int      perform_occur_based_simp;
        int      do_strengthen_with_occur;         ///<Perform self-subsuming resolution
        unsigned maxRedLinkInSize;
        double maxOccurIrredMB;
        double maxOccurRedMB;
        double maxOccurRedLitLinkedM;
        double   subsume_gothrough_multip;

        //Distillation
        int      do_distill_clauses;
        unsigned long long distill_long_cls_time_limitM;
        long watch_cache_stamp_based_str_time_limitM;
        long long distill_time_limitM;

        //Memory savings
        int       doRenumberVars;
        int       doSaveMem;

        //Component handling
        int       doCompHandler;
        unsigned  handlerFromSimpNum;
        size_t    compVarLimit;
        unsigned long long  comp_find_time_limitM;


        //Misc Optimisations
        int      doStrSubImplicit;
        long long  subsume_implicit_time_limitM;
        long long  distill_implicit_with_implicit_time_limitM;

        //Gates
        int      doGateFind; ///< Find OR gates
        unsigned maxGateBasedClReduceSize;
        int      doShortenWithOrGates; ///<Shorten clauses with or gates during subsumption
        int      doRemClWithAndGates; ///<Remove clauses using and gates during subsumption
        int      doFindEqLitsWithGates; ///<Find equivalent literals using gates during subsumption
        long long gatefinder_time_limitM;
        long long shorten_with_gates_time_limitM;
        long long remove_cl_with_gates_time_limitM;

        //Gauss
        GaussConf gaussconf;
        bool dont_elim_xor_vars;

        //Greedy undef
        int      greedy_undef;
        std::vector<uint32_t>* independent_vars;

        //Timeouts
        double orig_global_timeout_multiplier;
        double global_timeout_multiplier;
        double global_timeout_multiplier_multiplier;
        double global_multiplier_multiplier_max;
        double var_and_mem_out_mult;

        //Misc
        unsigned origSeed;
        unsigned long long sync_every_confl;
        unsigned reconfigure_val;
        unsigned reconfigure_at;
        unsigned preprocess;
        int      simulate_drat;
        std::string simplified_cnf;
        std::string solution_file;
        std::string saved_state_file;
};

} //end namespace

#endif //SOLVERCONF_H

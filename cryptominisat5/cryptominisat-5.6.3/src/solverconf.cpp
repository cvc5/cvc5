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

#include "constants.h"
#include "solverconf.h"
#include <limits>
#include <iomanip>
#include <sstream>
using namespace CMSat;

DLL_PUBLIC SolverConf::SolverConf() :
        //Variable activities
        var_inc_vsids_start(1)
        , var_decay_vsids_start(0.8) // 1/0.8 = 1.2 -- large is better for frequent restarts
        , var_decay_vsids_max(0.95) // 1/0.95 = 1.05 -- smaller is better for hard instances
        , random_var_freq(0)
        , polarity_mode(PolarityMode::polarmode_automatic)

        //Clause cleaning
        , every_lev1_reduce(10000) // kept for a while then moved to lev2
        , every_lev2_reduce(15000) // cleared regularly
        , must_touch_lev1_within(30000)

        , max_temp_lev2_learnt_clauses(30000) //only used if every_lev2_reduce==0
        , inc_max_temp_lev2_red_cls(1.0)      //only used if every_lev2_reduce==0
        , protect_cl_if_improved_glue_below_this_glue_for_one_turn(30)
        , glue_put_lev0_if_below_or_eq(3) // never removed
        , glue_put_lev1_if_below_or_eq(6) // kept for a while then moved to lev2

        , clause_decay(0.999)
        , adjust_glue_if_too_many_low(0.7)
        , min_num_confl_adjust_glue_cutoff(150ULL*1000ULL)
        , guess_cl_effectiveness(0)

        //maple
        , maple(true)
        , modulo_maple_iter(3)
        , more_maple_bump_high_glue(false)

        //Restarting
        , restart_first(100)
        , restart_inc(1.1)
        , restartType(Restart::glue_geom)
        , do_blocking_restart(1)
        , blocking_restart_trail_hist_length(5000)
        , blocking_restart_multip(1.4)
        , broken_glue_restart(true)
        , local_glue_multiplier(0.80)
        , shortTermHistorySize (50)
        , lower_bound_for_blocking_restart(10000)
        , ratio_glue_geom(5)
        , more_more_with_cache(false)
        , more_more_with_stamp(false)
        , doAlwaysFMinim(false)

        //Clause minimisation
        , doRecursiveMinim (true)
        , doMinimRedMore(true)
        , doMinimRedMoreMore(false)
        , max_glue_more_minim(6)
        , max_size_more_minim(30)
        , more_red_minim_limit_cache(400)
        , more_red_minim_limit_binary(200)
        , max_num_lits_more_more_red_min(1)

        //Verbosity
        , verbosity        (0)
        , doPrintGateDot   (false)
        , print_full_restart_stat   (false)
        , print_all_restarts (false)
        , verbStats        (0)
        , do_print_times(1)
        , print_restart_line_every_n_confl(4096)

        //Limits
        , maxTime          (std::numeric_limits<double>::max())
        , max_confl         (std::numeric_limits<long>::max())

        //Glues
        , update_glues_on_analyze(true)

        //OTF
        , otfHyperbin      (true)
        , doOTFSubsume     (false)
        , doOTFSubsumeOnlyAtOrBelowGlue(5)

        //SQL
        , dump_individual_restarts_and_clauses(true)
        , dump_individual_cldata_ratio(0.005)

        //Var-elim
        , doVarElim        (true)
        , varelim_cutoff_too_many_clauses(2000)
        , do_empty_varelim (true)
        , empty_varelim_time_limitM(300LL)
        , varelim_time_limitM(350)
        , varelim_sub_str_limit(600)
        , varElimRatioPerIter(1.60)
        , skip_some_bve_resolvents(true) //based on gates
        , velim_resolvent_too_large(20)

        //Subs, str limits for simplifier
        , subsumption_time_limitM(300)
        , strengthening_time_limitM(300)
        , aggressive_elim_time_limitM(300)

        //Bounded variable addition
        , do_bva(false)
        #ifdef USE_GAUSS
        , min_bva_gain(2)
        #else
        , min_bva_gain(32)
        #endif
        , bva_limit_per_call(150000)
        , bva_also_twolit_diff(true)
        , bva_extra_lit_and_red_start(0)
        , bva_time_limitM(100)

        //Probing
        , doProbe          (false)
        , doIntreeProbe    (true)
        , probe_bogoprops_time_limitM  (800ULL)
        , intree_time_limitM(1200ULL)
        , intree_scc_varreplace_time_limitM(30ULL)
        , doBothProp       (true)
        , doTransRed       (true)
        , doStamp          (false)
        , doCache          (false)
        , cacheUpdateCutoff(2000)
        , maxCacheSizeMB   (2048)
        , otf_hyper_time_limitM(340)
        , otf_hyper_ratio_limit(0.5) //if higher(closer to 1), we allow for less hyper-bin addition, i.e. we are stricter
        , single_probe_time_limit_perc(0.5)

        //XOR
        , doFindXors       (true)
        , maxXorToFind     (5)
        , useCacheWhenFindingXors(false)
        , doEchelonizeXOR  (true)
        , maxXORMatrix     (400ULL)
        #ifndef USE_GAUSS
        , xor_finder_time_limitM(50)
        #else
        , xor_finder_time_limitM(400)
        #endif
        , allow_elim_xor_vars(1)
        , xor_var_per_cut(2)

        //Var-replacer
        , doFindAndReplaceEqLits(true)
        , doExtendedSCC         (true)
        , max_scc_depth (10000)

        //Iterative Alo Scheduling
        , simplify_at_startup(false)
        , simplify_at_every_startup(false)
        , do_simplify_problem(true)
        , full_simplify_at_startup(false)
        , never_stop_search(false)
        , num_conflicts_of_search(50ULL*1000ULL)
        , num_conflicts_of_search_inc(1.4)
        , num_conflicts_of_search_inc_max(10)
        , simplify_schedule_startup(
            "sub-impl,"
            "occ-backw-sub-str, occ-clean-implicit, occ-bve,"
            "occ-backw-sub-str, occ-xor,"
            "scc-vrepl,"
            "sub-cls-with-bin,"
        )
        , simplify_schedule_nonstartup(
            "handle-comps,"
            "scc-vrepl, cache-clean, cache-tryboth,"
            "sub-impl, intree-probe, probe,"
            "sub-str-cls-with-bin, distill-cls,"
            "scc-vrepl, sub-impl, str-impl, sub-impl,"
            "occ-backw-sub-str, occ-clean-implicit, occ-bve, occ-bva, "//occ-gates,"
            "occ-xor,"
            "str-impl, cache-clean, sub-str-cls-with-bin, distill-cls,"
            "scc-vrepl, check-cache-size, renumber,"
        )
        , simplify_schedule_preproc(
            "handle-comps,"
            "scc-vrepl, cache-clean, cache-tryboth,"
            "sub-impl,"
            "sub-str-cls-with-bin, distill-cls, scc-vrepl, sub-impl,"
            "occ-backw-sub-str, occ-xor, occ-clean-implicit, occ-bve, occ-bva,"
            //"occ-gates,"
            "str-impl, cache-clean, sub-str-cls-with-bin, distill-cls, scc-vrepl, sub-impl,"
            "str-impl, sub-impl, sub-str-cls-with-bin,"
            "intree-probe, probe,"
            "must-renumber"
        )

        //Occur based simplification
        , perform_occur_based_simp(true)
        , do_strengthen_with_occur       (true)
        , maxRedLinkInSize (200)
        , maxOccurIrredMB  (2500)
        , maxOccurRedMB    (600)
        , maxOccurRedLitLinkedM(50)
        , subsume_gothrough_multip(2.0)

        //Distillation
        , do_distill_clauses(true)
        , distill_long_cls_time_limitM(20ULL)
        , watch_cache_stamp_based_str_time_limitM(30LL)
        , distill_time_limitM(120LL)

        //Memory savings
        , doRenumberVars   (true)
        , doSaveMem        (true)

        //Component finding
        , doCompHandler    (false)
        , handlerFromSimpNum (0)
        , compVarLimit      (1ULL*1000ULL*1000ULL)
        , comp_find_time_limitM (500)

        //Misc optimisations
        , doStrSubImplicit (true)
        , subsume_implicit_time_limitM(100LL)
        , distill_implicit_with_implicit_time_limitM(200LL)

        //Gates
        , doGateFind       (false)
        , maxGateBasedClReduceSize(20)
        , doShortenWithOrGates(true)
        , doRemClWithAndGates(true)
        , doFindEqLitsWithGates(true)
        , gatefinder_time_limitM(200)
        , shorten_with_gates_time_limitM(200)
        , remove_cl_with_gates_time_limitM(100)

        //Greedy Undef
        , greedy_undef(false)
        , independent_vars (NULL)

        //Timeouts
        , orig_global_timeout_multiplier(4.0)
        , global_timeout_multiplier(1.0) // WILL BE UNSET, NOT RELEVANT
        , global_timeout_multiplier_multiplier(1.1)
        , global_multiplier_multiplier_max(3)
        , var_and_mem_out_mult(1.0)

        //misc
        , origSeed(0)
        , sync_every_confl(20000)
        , reconfigure_val(0)
        , reconfigure_at(2)
        , preprocess(0)
        , simulate_drat(false)
        , saved_state_file("savedstate.dat")
{
    ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
    ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.44;
}


DLL_PUBLIC std::string SolverConf::print_times(
    const double time_used
    , const bool time_out
    , const double time_remain
) const {
    if (do_print_times) {
        std::stringstream ss;
        ss
        << " T: " << std::setprecision(2) << std::fixed << time_used
        << " T-out: " << (time_out ? "Y" : "N")
        << " T-r: " << time_remain*100.0  << "%";

        return ss.str();
    }

    return std::string();
}

DLL_PUBLIC std::string SolverConf::print_times(
    const double time_used
    , const bool time_out
) const {
    if (do_print_times) {
        std::stringstream ss;
        ss
        << " T: " << std::setprecision(2) << std::fixed << time_used
        << " T-out: " << (time_out ? "Y" : "N");

        return ss.str();
    }

    return std::string();
}

DLL_PUBLIC std::string SolverConf::print_times(
    const double time_used
) const {
    if (do_print_times) {
        std::stringstream ss;
        ss
        << " T: " << std::setprecision(2) << std::fixed << time_used;

        return ss.str();
    }

    return std::string();
}

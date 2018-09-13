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
#include "cryptominisat5/cryptominisat.h"
#include "solver.h"
#include "drat.h"
#include "shareddata.h"
#include <fstream>

#include <thread>
#include <mutex>
#include <atomic>
using std::thread;

#define CACHE_SIZE 10ULL*1000ULL*1000UL
#ifndef LIMITMEM
#define MAX_VARS (1ULL<<28)
#else
#define MAX_VARS 3000
#endif

using namespace CMSat;

static bool print_thread_start_and_finish = false;

namespace CMSat {
    struct CMSatPrivateData {
        explicit CMSatPrivateData(std::atomic<bool>* _must_interrupt)
        {
            must_interrupt = _must_interrupt;
            if (must_interrupt == NULL) {
                must_interrupt = new std::atomic<bool>(false);
                must_interrupt_needs_delete = true;
            }
        }
        ~CMSatPrivateData()
        {
            for(Solver* this_s: solvers) {
                delete this_s;
            }
            if (must_interrupt_needs_delete) {
                delete must_interrupt;
            }

            delete log; //this will also close the file
            delete shared_data;
        }
        CMSatPrivateData(const CMSatPrivateData&) = delete;
        CMSatPrivateData& operator=(const CMSatPrivateData&) = delete;

        vector<Solver*> solvers;
        SharedData *shared_data = NULL;
        int which_solved = 0;
        std::atomic<bool>* must_interrupt;
        bool must_interrupt_needs_delete = false;
        unsigned cls = 0;
        unsigned vars_to_add = 0;
        vector<Lit> cls_lits;
        bool okay = true;
        std::ofstream* log = NULL;
        int sql = 0;
        double timeout = std::numeric_limits<double>::max();

        uint64_t previous_sum_conflicts = 0;
        uint64_t previous_sum_propagations = 0;
        uint64_t previous_sum_decisions = 0;
    };
}

struct DataForThread
{
    explicit DataForThread(CMSatPrivateData* data, const vector<Lit>* _assumptions = NULL) :
        solvers(data->solvers)
        , lits_to_add(&(data->cls_lits))
        , vars_to_add(data->vars_to_add)
        , assumptions(_assumptions)
        , update_mutex(new std::mutex)
        , which_solved(&(data->which_solved))
        , ret(new lbool(l_Undef))
    {
    }

    ~DataForThread()
    {
        delete update_mutex;
        delete ret;
    }
    vector<Solver*>& solvers;
    vector<Lit> *lits_to_add;
    uint32_t vars_to_add;
    const vector<Lit> *assumptions;
    std::mutex* update_mutex;
    int *which_solved;
    lbool* ret;
};

DLL_PUBLIC SATSolver::SATSolver(
    void* config
    , std::atomic<bool>* interrupt_asap
    )
{
    data = new CMSatPrivateData(interrupt_asap);

    if (config && ((SolverConf*) config)->verbosity) {
        //NOT SAFE
        //yes -- this system will use a lock, but the solver itself won't(!)
        //so things will get mangled and printed wrongly
        //print_thread_start_and_finish = true;
    }

    data->solvers.push_back(new Solver((SolverConf*) config, data->must_interrupt));
}

DLL_PUBLIC SATSolver::~SATSolver()
{
    delete data;
}

void update_config(SolverConf& conf, unsigned thread_num)
{
    //Don't accidentally reconfigure everything to a specific value!
    if (thread_num > 0) {
        conf.reconfigure_val = 0;
    }
    conf.origSeed += thread_num;

    switch(thread_num % 23) {
        case 0: {
            //default setup
            break;
        }

        case 1: {
            //Minisat-like
            conf.maple = 0;
            conf.varElimRatioPerIter = 1;
            conf.restartType = Restart::geom;
            conf.polarity_mode = CMSat::PolarityMode::polarmode_neg;

            conf.inc_max_temp_lev2_red_cls = 1.02;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.5;
            break;
        }
        case 2: {
            conf.maple = 1;
            conf.modulo_maple_iter = 100;
            break;
        }
        case 3: {
            //Similar to CMS 2.9 except we look at learnt DB size insteead
            //of conflicts to see if we need to clean.
            conf.maple = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0.5;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0;
            conf.glue_put_lev0_if_below_or_eq = 0;
            conf.inc_max_temp_lev2_red_cls = 1.03;
            break;
        }
        case 4: {
            //Similar to CMS 5.0
            conf.maple = 0;
            conf.varElimRatioPerIter = 0.4;
            conf.every_lev1_reduce = 0;
            conf.every_lev2_reduce = 0;
            conf.max_temp_lev2_learnt_clauses = 30000;
            conf.glue_put_lev0_if_below_or_eq = 4;

            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.5;
            break;
        }
        case 5: {
            conf.maple = 0;
            conf.never_stop_search = true;
            break;
        }
        case 6: {
            //Maple with backtrack
            conf.maple = 1;
            conf.modulo_maple_iter = 100;
            break;
        }
        case 7: {
            conf.maple = 0;
            conf.do_bva = true;
            conf.glue_put_lev0_if_below_or_eq = 2;
            conf.varElimRatioPerIter = 1;
            conf.inc_max_temp_lev2_red_cls = 1.04;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0.1;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.3;
            conf.var_decay_vsids_max = 0.90; //more 'slow' in adjusting activities
            break;
        }
        case 8: {
            //Different glue limit
            conf.maple = 0;
            conf.glue_put_lev0_if_below_or_eq = 2;
            conf.glue_put_lev1_if_below_or_eq = 2;
            break;
        }
        case 9: {
            conf.maple = 0;
            conf.var_decay_vsids_max = 0.998;
            break;
        }
        case 10: {
            conf.maple = 0;
            conf.polarity_mode = CMSat::PolarityMode::polarmode_pos;
            break;
        }
        case 11: {
            conf.maple = 0;
            conf.varElimRatioPerIter = 1;
            conf.restartType = Restart::geom;

            conf.inc_max_temp_lev2_red_cls = 1.01;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.3;
            break;
        }
        case 12: {
            conf.maple = 0;
            conf.inc_max_temp_lev2_red_cls = 1.001;
            break;
        }

        case 13: {
            //Minisat-like
            conf.maple = 1;
            conf.varElimRatioPerIter = 1;
            conf.restartType = Restart::geom;
            conf.polarity_mode = CMSat::PolarityMode::polarmode_neg;

            conf.inc_max_temp_lev2_red_cls = 1.02;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.5;
            break;
        }
        case 14: {
            //Different glue limit
            conf.maple = 0;
            conf.doMinimRedMoreMore = 1;
            conf.glue_put_lev0_if_below_or_eq = 4;
            //conf.glue_put_lev2_if_below_or_eq = 8;
            conf.max_num_lits_more_more_red_min = 3;
            conf.max_glue_more_minim = 4;
            break;
        }
        case 15: {
            //Similar to CMS 2.9 except we look at learnt DB size insteead
            //of conflicts to see if we need to clean.
            conf.maple = 1;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0.5;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0;
            conf.glue_put_lev0_if_below_or_eq = 0;
            conf.inc_max_temp_lev2_red_cls = 1.03;
            break;
        }
        case 16: {
            //Similar to CMS 5.0
            conf.maple = 1;
            conf.varElimRatioPerIter = 0.4;
            conf.every_lev1_reduce = 0;
            conf.every_lev2_reduce = 0;
            conf.max_temp_lev2_learnt_clauses = 30000;
            conf.glue_put_lev0_if_below_or_eq = 4;

            conf.ratio_keep_clauses[clean_to_int(ClauseClean::glue)] = 0;
            conf.ratio_keep_clauses[clean_to_int(ClauseClean::activity)] = 0.5;
            break;
        }
        case 17: {
            //conf.max_temporary_learnt_clauses = 10000;
            conf.do_bva = true;
            break;
        }
        case 18: {
            conf.maple = 0;
            conf.every_lev1_reduce = 0;
            conf.every_lev2_reduce = 0;
            conf.glue_put_lev1_if_below_or_eq = 0;
            conf.max_temp_lev2_learnt_clauses = 10000;
            break;
        }

        case 19: {
            conf.maple = 1;
            conf.doMinimRedMoreMore = 1;
            conf.orig_global_timeout_multiplier = 5;
            conf.num_conflicts_of_search_inc = 1.15;
            conf.more_red_minim_limit_cache = 1200;
            conf.more_red_minim_limit_binary = 600;
            conf.max_num_lits_more_more_red_min = 20;
            //conf.max_temporary_learnt_clauses = 10000;
            conf.var_decay_vsids_max = 0.99; //more 'fast' in adjusting activities
            break;
        }

        case 20: {
            //Luby
            conf.maple = 0;
            conf.restart_inc = 1.5;
            conf.restart_first = 100;
            conf.restartType = CMSat::Restart::luby;
            break;
        }

        case 21: {
            conf.maple = 0;
            conf.glue_put_lev0_if_below_or_eq = 3;
            conf.glue_put_lev1_if_below_or_eq = 5;
            conf.var_decay_vsids_max = 0.97;
            break;
        }

        case 22: {
            conf.maple = 0;
            conf.doMinimRedMoreMore = 1;
            conf.orig_global_timeout_multiplier = 5;
            conf.num_conflicts_of_search_inc = 1.15;
            conf.more_red_minim_limit_cache = 1200;
            conf.more_red_minim_limit_binary = 600;
            conf.max_num_lits_more_more_red_min = 20;
            //conf.max_temporary_learnt_clauses = 10000;
            conf.var_decay_vsids_max = 0.99; //more 'fast' in adjusting activities
            break;
        }

        default: {
            conf.maple = ((thread_num % 3) <= 1);
            conf.modulo_maple_iter = (thread_num % 7)+1;
            conf.varElimRatioPerIter = 0.1*(thread_num % 9);
            if (thread_num % 4 == 0) {
                conf.restartType = Restart::glue;
            }
            if (thread_num % 5 == 0) {
                conf.restartType = Restart::geom;
            }
            conf.restart_first = 100 * (0.5*(thread_num % 5));
            conf.doMinimRedMoreMore = ((thread_num % 5) == 1);
            break;
        }
    }
}

DLL_PUBLIC void SATSolver::set_num_threads(unsigned num)
{
    if (num <= 0) {
        std::cerr << "ERROR: Number of threads must be at least 1" << endl;
        throw std::runtime_error("ERROR: Number of threads must be at least 1");
    }
    if (num == 1) {
        return;
    }

    if (data->solvers[0]->drat->enabled() ||
        data->solvers[0]->conf.simulate_drat
    ) {
        std::cerr << "ERROR: DRAT cannot be used in multi-threaded mode" << endl;
        throw std::runtime_error("ERROR: DRAT cannot be used in multi-threaded mode");
    }

    if (data->cls > 0 || nVars() > 0) {
        std::cerr << "ERROR: You must first call set_num_threads() and only then add clauses and variables" << endl;
        throw std::runtime_error("ERROR: You must first call set_num_threads() and only then add clauses and variables");
    }

    data->cls_lits.reserve(CACHE_SIZE);
    for(unsigned i = 1; i < num; i++) {
        SolverConf conf = data->solvers[0]->getConf();
        update_config(conf, i);
        data->solvers.push_back(new Solver(&conf, data->must_interrupt));
    }

    //set shared data
    data->shared_data = new SharedData(data->solvers.size());
    for(unsigned i = 0; i < num; i++) {
        SolverConf conf = data->solvers[i]->getConf();
        if (i >= 1) {
            conf.verbosity = 0;
            conf.doFindXors = 0;
        }
        data->solvers[i]->setConf(conf);
        data->solvers[i]->set_shared_data((SharedData*)data->shared_data);
    }
}

struct OneThreadAddCls
{
    OneThreadAddCls(DataForThread& _data_for_thread, size_t _tid) :
        data_for_thread(_data_for_thread)
        , tid(_tid)
    {
    }

    void operator()()
    {
        Solver& solver = *data_for_thread.solvers[tid];
        solver.new_external_vars(data_for_thread.vars_to_add);

        vector<Lit> lits;
        vector<uint32_t> vars;
        bool ret = true;
        size_t at = 0;
        const vector<Lit>& orig_lits = (*data_for_thread.lits_to_add);
        const size_t size = orig_lits.size();
        while(at < size && ret) {
            if (orig_lits[at] == lit_Undef) {
                lits.clear();
                at++;
                for(; at < size
                    && orig_lits[at] != lit_Undef
                    && orig_lits[at] != lit_Error
                    ; at++
                ) {
                    lits.push_back(orig_lits[at]);
                }
                ret = solver.add_clause_outer(lits);
            } else {
                vars.clear();
                at++;
                bool rhs = orig_lits[at].sign();
                at++;
                for(; at < size
                    && orig_lits[at] != lit_Undef
                    && orig_lits[at] != lit_Error
                    ; at++
                ) {
                    vars.push_back(orig_lits[at].var());
                }
                ret = solver.add_xor_clause_outer(vars, rhs);
            }
        }

        if (!ret) {
            data_for_thread.update_mutex->lock();
            *data_for_thread.ret = l_False;
            data_for_thread.update_mutex->unlock();
        }
    }

    DataForThread& data_for_thread;
    const size_t tid;
};

static bool actually_add_clauses_to_threads(CMSatPrivateData* data)
{
    DataForThread data_for_thread(data);
    std::vector<std::thread> thds;
    for(size_t i = 0; i < data->solvers.size(); i++) {
        thds.push_back(thread(OneThreadAddCls(data_for_thread, i)));
    }
    for(std::thread& thread : thds){
        thread.join();
    }
    bool ret = (*data_for_thread.ret == l_True);

    //clear what has been added
    data->cls_lits.clear();
    data->vars_to_add = 0;

    return ret;
}

DLL_PUBLIC void SATSolver::set_max_time(double max_time)
{
  for (size_t i = 0; i < data->solvers.size(); ++i) {
    Solver& s = *data->solvers[i];
    if (max_time >= 0) {
      s.conf.maxTime = s.get_stats().cpu_time + max_time;
    }
  }
}

DLL_PUBLIC void SATSolver::set_max_confl(int64_t max_confl)
{
  for (size_t i = 0; i < data->solvers.size(); ++i) {
    Solver& s = *data->solvers[i];
    if (max_confl >= 0) {
      s.conf.max_confl = s.get_stats().conflStats.numConflicts + max_confl;
    }
  }
}

DLL_PUBLIC void SATSolver::set_default_polarity(bool polarity)
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.polarity_mode = polarity ? PolarityMode::polarmode_pos : PolarityMode::polarmode_neg;
    }
}

DLL_PUBLIC void SATSolver::set_no_simplify()
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.doRenumberVars = false;
        s.conf.simplify_at_startup = false;
        s.conf.simplify_at_every_startup = false;
        s.conf.full_simplify_at_startup = false;
        s.conf.perform_occur_based_simp = false;
        s.conf.do_simplify_problem = false;
    }
}

DLL_PUBLIC void SATSolver::set_allow_otf_gauss()
{
    #ifndef USE_GAUSS
    std::cerr << "ERROR: CryptoMiniSat was not compiled with GAUSS" << endl;
    exit(-1);
    #else
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        //s.conf.reconfigure_at = 0;
        //s.conf.reconfigure_val = 15;
        s.conf.gaussconf.max_num_matrixes = 10;
        s.conf.gaussconf.autodisable = false;
        s.conf.allow_elim_xor_vars = false;
    }
    #endif
}

DLL_PUBLIC void SATSolver::set_no_simplify_at_startup()
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.simplify_at_startup = false;
    }
}

DLL_PUBLIC void SATSolver::set_no_equivalent_lit_replacement()
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.doFindAndReplaceEqLits = false;
    }
}

DLL_PUBLIC void SATSolver::set_no_bva()
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.do_bva = false;
    }
}

DLL_PUBLIC void SATSolver::set_no_bve()
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.doVarElim = false;
    }
}

DLL_PUBLIC void SATSolver::set_greedy_undef()
{
    assert(false && "ERROR: Unfortunately, greedy undef is broken, please don't use it");
    std::cerr << "ERROR: Unfortunately, greedy undef is broken, please don't use it" << endl;
    exit(-1);

    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.greedy_undef = true;
    }
}

DLL_PUBLIC void SATSolver::set_independent_vars(vector<uint32_t>* ind_vars)
{
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        s.conf.independent_vars = ind_vars;
    }
}


DLL_PUBLIC void SATSolver::set_verbosity(unsigned verbosity)
{
    if (data->solvers.empty())
        return;

    Solver& s = *data->solvers[0];
    s.conf.verbosity = verbosity;
}

DLL_PUBLIC void SATSolver::set_timeout_all_calls(double timeout)
{
    data->timeout = timeout;
}

DLL_PUBLIC bool SATSolver::add_clause(const vector< Lit >& lits)
{
    if (data->log) {
        (*data->log) << lits << " 0" << endl;
    }

    bool ret = true;
    if (data->solvers.size() > 1) {
        if (data->cls_lits.size() + lits.size() + 1 > CACHE_SIZE) {
            ret = actually_add_clauses_to_threads(data);
        }

        data->cls_lits.push_back(lit_Undef);
        for(Lit lit: lits) {
            data->cls_lits.push_back(lit);
        }
    } else {
        data->solvers[0]->new_vars(data->vars_to_add);
        data->vars_to_add = 0;

        ret = data->solvers[0]->add_clause_outer(lits);
        data->cls++;
    }

    return ret;
}

void add_xor_clause_to_log(const std::vector<unsigned>& vars, bool rhs, std::ofstream* file)
{
    if (vars.size() == 0) {
        if (rhs) {
            (*file) << "0" << endl;;
        }
    } else {
        if (!rhs) {
            (*file) << "-";
        }
        for(unsigned var: vars) {
            (*file) << (var+1) << " ";
        }
        (*file) << " 0" << endl;;
    }
}

DLL_PUBLIC bool SATSolver::add_xor_clause(const std::vector<unsigned>& vars, bool rhs)
{
    if (data->log) {
       add_xor_clause_to_log(vars, rhs, data->log);
    }

    bool ret = true;
    if (data->solvers.size() > 1) {
        if (data->cls_lits.size() + vars.size() + 1 > CACHE_SIZE) {
            ret = actually_add_clauses_to_threads(data);
        }

        data->cls_lits.push_back(lit_Error);
        data->cls_lits.push_back(Lit(0, rhs));
        for(uint32_t var: vars) {
            data->cls_lits.push_back(Lit(var, false));
        }
    } else {
        data->solvers[0]->new_vars(data->vars_to_add);
        data->vars_to_add = 0;

        ret = data->solvers[0]->add_xor_clause_outer(vars, rhs);
        data->cls++;
    }

    return ret;
}

struct OneThreadCalc
{
    OneThreadCalc(
        DataForThread& _data_for_thread,
        size_t _tid,
        bool _solve,
        bool _only_indep_solution
    ) :
        data_for_thread(_data_for_thread)
        , tid(_tid)
        , solve(_solve)
        , only_indep_solution(_only_indep_solution)
    {}

    void operator()()
    {
        if (print_thread_start_and_finish) {
            start_time = cpuTime();
            //data_for_thread.update_mutex->lock();
            //cout << "c Starting thread " << tid << endl;
            //data_for_thread.update_mutex->unlock();
        }

        OneThreadAddCls cls_adder(data_for_thread, tid);
        cls_adder();
        lbool ret;
        if (solve) {
            ret = data_for_thread.solvers[tid]->solve_with_assumptions(data_for_thread.assumptions, only_indep_solution);
        } else {
            ret = data_for_thread.solvers[tid]->simplify_with_assumptions(data_for_thread.assumptions);
        }

        if (print_thread_start_and_finish) {
            double end_time = cpuTime();
            data_for_thread.update_mutex->lock();
            ios::fmtflags f(cout.flags());
            cout << "c Finished thread " << tid << " with result: " << ret
            << " T-diff: " << std::fixed << std::setprecision(2)
            << (end_time-start_time)
            << endl;
            cout.flags(f);
            data_for_thread.update_mutex->unlock();
        }


        if (ret != l_Undef) {
            data_for_thread.update_mutex->lock();
            *data_for_thread.which_solved = tid;
            *data_for_thread.ret = ret;
            //will interrupt all of them
            data_for_thread.solvers[0]->set_must_interrupt_asap();
            data_for_thread.update_mutex->unlock();
        }
    }

    DataForThread& data_for_thread;
    const size_t tid;
    double start_time;
    bool solve;
    bool only_indep_solution;
};

lbool calc(
    const vector< Lit >* assumptions,
    bool solve, CMSatPrivateData *data,
    bool only_indep_solution = false
) {
    //Reset the interrupt signal if it was set
    data->must_interrupt->store(false, std::memory_order_relaxed);

    //Set timeout information
    if (data->timeout != std::numeric_limits<double>::max()) {
        for (size_t i = 0; i < data->solvers.size(); ++i) {
            Solver& s = *data->solvers[i];
            s.conf.maxTime = cpuTime() + data->timeout;
        }
    }

    if (data->log) {
        (*data->log) << "c Solver::"
        << (solve ? "solve" : "simplify")
        << "( ";
        if (assumptions) {
            (*data->log) << *assumptions;
        }
        (*data->log) << " )" << endl;
    }

    if (data->solvers.size() > 1 && data->sql > 0) {
        std::cerr
        << "Multithreaded solving and SQL cannot be specified at the same time"
        << endl;
        exit(-1);
    }

    if (data->solvers.size() == 1) {
        data->solvers[0]->new_vars(data->vars_to_add);
        data->vars_to_add = 0;

        lbool ret ;
        if (solve) {
            ret = data->solvers[0]->solve_with_assumptions(assumptions, only_indep_solution);
        } else {
            ret = data->solvers[0]->simplify_with_assumptions(assumptions);
        }
        data->okay = data->solvers[0]->okay();
        return ret;
    }

    //Multi-thread from now on.
    DataForThread data_for_thread(data, assumptions);
    std::vector<std::thread> thds;
    for(size_t i = 0
        ; i < data->solvers.size()
        ; i++
    ) {
        thds.push_back(thread(OneThreadCalc(data_for_thread, i, solve, only_indep_solution)));
    }
    for(std::thread& thread : thds){
        thread.join();
    }
    lbool real_ret = *data_for_thread.ret;

    //This does it for all of them, there is only one must-interrupt
    data_for_thread.solvers[0]->unset_must_interrupt_asap();

    //clear what has been added
    data->cls_lits.clear();
    data->vars_to_add = 0;
    data->okay = data->solvers[*data_for_thread.which_solved]->okay();
    return real_ret;
}

DLL_PUBLIC lbool SATSolver::solve(const vector< Lit >* assumptions, bool only_indep_solution)
{
    //set information data (props, confl, dec)
    data->previous_sum_conflicts = get_sum_conflicts();
    data->previous_sum_propagations = get_sum_propagations();
    data->previous_sum_decisions = get_sum_decisions();

    return calc(assumptions, true, data, only_indep_solution);
}

DLL_PUBLIC lbool SATSolver::simplify(const vector< Lit >* assumptions)
{
    //set information data (props, confl, dec)
    data->previous_sum_conflicts = get_sum_conflicts();
    data->previous_sum_propagations = get_sum_propagations();
    data->previous_sum_decisions = get_sum_decisions();

    return calc(assumptions, false, data);
}

DLL_PUBLIC const vector< lbool >& SATSolver::get_model() const
{
    return data->solvers[data->which_solved]->get_model();
}

DLL_PUBLIC const std::vector<Lit>& SATSolver::get_conflict() const
{

    return data->solvers[data->which_solved]->get_final_conflict();
}

DLL_PUBLIC uint32_t SATSolver::nVars() const
{
    return data->solvers[0]->nVarsOutside() + data->vars_to_add;
}

DLL_PUBLIC void SATSolver::new_var()
{
    new_vars(1);
}

DLL_PUBLIC void SATSolver::new_vars(const size_t n)
{
    if (n >= MAX_VARS
        || (data->vars_to_add + n) >= MAX_VARS
    ) {
        throw CMSat::TooManyVarsError();
    }

    if (data->log) {
        (*data->log) << "c Solver::new_vars( " << n << " )" << endl;
    }

    data->vars_to_add += n;
}

DLL_PUBLIC void SATSolver::add_sql_tag(const std::string& tagname, const std::string& tag)
{
    for(Solver* solver: data->solvers) {
        solver->add_sql_tag(tagname, tag);
    }
}


DLL_PUBLIC const char* SATSolver::get_version_sha1()
{
    return Solver::get_version_sha1();
}

DLL_PUBLIC const char* SATSolver::get_version()
{
    return Solver::get_version_tag();
}

DLL_PUBLIC const char* SATSolver::get_compilation_env()
{
    return Solver::get_compilation_env();
}

DLL_PUBLIC void SATSolver::print_stats() const
{
    double cpu_time;
    if (data->solvers.size() > 1) {
        cpu_time = cpuTimeTotal();
    } else {
        cpu_time = cpuTime();
    }
    data->solvers[data->which_solved]->print_stats(cpu_time);
}

DLL_PUBLIC void SATSolver::set_drat(std::ostream* os, bool add_ID)
{
    if (data->solvers.size() > 1) {
        std::cerr << "ERROR: DRAT cannot be used in multi-threaded mode" << endl;
        exit(-1);
    }
    Drat* drat = NULL;
    if (add_ID) {
        drat = new DratFile<true>;
    } else {
        drat = new DratFile<false>;
    }
    drat->setFile(os);
    if (data->solvers[0]->drat)
        delete data->solvers[0]->drat;

    data->solvers[0]->drat = drat;
}

DLL_PUBLIC void SATSolver::interrupt_asap()
{
    data->must_interrupt->store(true, std::memory_order_relaxed);
}

void DLL_PUBLIC SATSolver::add_in_partial_solving_stats()
{
    data->solvers[data->which_solved]->add_in_partial_solving_stats();
}

DLL_PUBLIC std::vector<Lit> SATSolver::get_zero_assigned_lits() const
{
    return data->solvers[data->which_solved]->get_zero_assigned_lits();
}

DLL_PUBLIC unsigned long SATSolver::get_sql_id() const
{
    return data->solvers[0]->get_sql_id();
}

DLL_PUBLIC bool SATSolver::okay() const
{
    return data->okay;
}

DLL_PUBLIC void SATSolver::log_to_file(std::string filename)
{
    if (data->log) {
        std::cerr
        << "ERROR: A file has already been designated for logging!"
        << endl;
        exit(-1);
    }

    data->log = new std::ofstream();
    data->log->exceptions( std::ofstream::failbit | std::ofstream::badbit );
    data->log->open(filename.c_str(), std::ios::out);
    if (!data->log->is_open()) {
        std::cerr
        << "ERROR: Cannot open record file '" << filename << "'"
        << " for writing."
        << endl;
        exit(-1);
    }
}

DLL_PUBLIC std::vector<std::pair<Lit, Lit> > SATSolver::get_all_binary_xors() const
{
    return data->solvers[0]->get_all_binary_xors();
}

DLL_PUBLIC vector<std::pair<vector<uint32_t>, bool> >
SATSolver::get_recovered_xors(bool elongate) const
{
    vector<std::pair<vector<uint32_t>, bool> > ret;
    Solver& s = *data->solvers[0];

    std::pair<vector<uint32_t>, bool> tmp;
    vector<Xor> xors = s.get_recovered_xors(elongate);
    for(const auto& x: xors) {
        tmp.first = x.get_vars();
        tmp.second = x.rhs;
        ret.push_back(tmp);
    }
    return ret;
}

DLL_PUBLIC void SATSolver::set_sqlite(std::string filename)
{
    if (data->solvers.size() > 1) {
        std::cerr
        << "Multithreaded solving and SQL cannot be specified at the same time"
        << endl;
        exit(-1);
    }
    data->sql = 1;
    data->solvers[0]->set_sqlite(filename);
}

DLL_PUBLIC uint64_t SATSolver::get_sum_conflicts()
{
    uint64_t conlf = 0;
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        conlf += s.sumConflicts;
    }
    return conlf;
}

DLL_PUBLIC uint64_t SATSolver::get_sum_propagations()
{
    uint64_t props = 0;
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        props += s.sumPropStats.propagations;
    }
    return props;
}

DLL_PUBLIC uint64_t SATSolver::get_sum_decisions()
{
    uint64_t dec = 0;
    for (size_t i = 0; i < data->solvers.size(); ++i) {
        Solver& s = *data->solvers[i];
        dec += s.sumSearchStats.decisions;
    }
    return dec;
}

DLL_PUBLIC uint64_t SATSolver::get_last_conflicts()
{
    return get_sum_conflicts() - data->previous_sum_conflicts;
}

DLL_PUBLIC uint64_t SATSolver::get_last_propagations()
{
    return get_sum_propagations() - data->previous_sum_propagations;
}

DLL_PUBLIC uint64_t SATSolver::get_last_decisions()
{
    return get_sum_decisions() - data->previous_sum_decisions;
}

DLL_PUBLIC void SATSolver::open_file_and_dump_irred_clauses(std::string fname) const
{
    data->solvers[data->which_solved]->open_file_and_dump_irred_clauses(fname);
}

void DLL_PUBLIC SATSolver::open_file_and_dump_red_clauses(std::string fname) const
{
    data->solvers[data->which_solved]->open_file_and_dump_red_clauses(fname);
}

void DLL_PUBLIC SATSolver::start_getting_small_clauses(uint32_t max_len, uint32_t max_glue)
{
    assert(data->solvers.size() >= 1);
    data->solvers[0]->start_getting_small_clauses(max_len, max_glue);
}

bool DLL_PUBLIC SATSolver::get_next_small_clause(std::vector<Lit>& out)
{
    assert(data->solvers.size() >= 1);
    return data->solvers[0]->get_next_small_clause(out);
}

void DLL_PUBLIC SATSolver::end_getting_small_clauses()
{
    assert(data->solvers.size() >= 1);
    data->solvers[0]->end_getting_small_clauses();
}

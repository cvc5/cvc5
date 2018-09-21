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

#ifndef VARREPLACER_H
#define VARREPLACER_H

#include <map>
#include <vector>
#include <utility>

#include "constants.h"
#include "solvertypes.h"
#include "clause.h"
#include "watcharray.h"
#include "simplefile.h"

namespace CMSat {

//#define VERBOSE_DEBUG

using std::map;
using std::vector;
class Solver;
class SCCFinder;

/**
@brief Replaces variables with their anti/equivalents
*/
class VarReplacer
{
    public:
        explicit VarReplacer(Solver* solver);
        ~VarReplacer();
        void new_var(const uint32_t orig_outer);
        void new_vars(const size_t n);
        void save_on_var_memory();
        bool replace_if_enough_is_found(const size_t limit = 0, uint64_t* bogoprops = NULL, bool* replaced = NULL);
        uint32_t print_equivalent_literals(bool outer_numbering, std::ostream *os = NULL) const;
        void print_some_stats(const double global_cpu_time) const;
        const SCCFinder* get_scc_finder() const;

        void extend_model_already_set();
        void extend_model_set_undef();
        void extend_model(const uint32_t var);

        uint32_t get_var_replaced_with(const uint32_t var) const;
        uint32_t get_var_replaced_with(const Lit lit) const;
        Lit get_lit_replaced_with(Lit lit) const;
        Lit get_lit_replaced_with_outer(Lit lit) const;
        uint32_t get_var_replaced_with_outer(uint32_t var) const;
        bool var_is_replacing(const uint32_t var);

        vector<uint32_t> get_vars_replacing(uint32_t var) const;
        void updateVars(
            const vector<uint32_t>& outerToInter
            , const vector<uint32_t>& interToOuter
        );

        //Stats
        size_t get_num_replaced_vars() const;
        struct Stats
        {
            void clear()
            {
                Stats tmp;
                *this = tmp;
            }

            Stats& operator+=(const Stats& other);
            void print(const size_t nVars) const;
            void print_short(const Solver* solver) const;

            uint64_t numCalls = 0;
            double cpu_time = 0;
            uint64_t replacedLits = 0;
            uint64_t zeroDepthAssigns = 0;
            uint64_t actuallyReplacedVars = 0;
            uint64_t removedBinClauses = 0;
            uint64_t removedLongClauses = 0;
            uint64_t removedLongLits = 0;
            uint64_t bogoprops = 0;
        };
        const Stats& get_stats() const;
        size_t mem_used() const;
        vector<std::pair<Lit, Lit> > get_all_binary_xors_outer() const;
        vector<uint32_t> get_vars_replacing_others() const;
        bool get_scc_depth_warning_triggered() const;

        void save_state(SimpleOutFile& f) const;
        void load_state(SimpleInFile& f);

    private:
        Solver* solver;
        SCCFinder* scc_finder;
        vector<Clause*> delayed_attach_or_free;

        void check_no_replaced_var_set() const;
        vector<Lit> fast_inter_replace_lookup;
        void build_fast_inter_replace_lookup();
        void destroy_fast_inter_replace_lookup();
        Lit get_lit_replaced_with_fast(const Lit lit) const {
            return fast_inter_replace_lookup[lit.var()] ^ lit.sign();
        }
        uint32_t get_var_replaced_with_fast(const uint32_t var) const {
            return fast_inter_replace_lookup[var].var();
        }
        bool replace_xor_clauses();

        vector<Lit> ps_tmp;
        bool perform_replace();
        bool add_xor_as_bins(const BinaryXor& bin_xor);
        bool replace(
            uint32_t lit1
            , uint32_t lit2
            , bool xor_is_true
        );

        bool isReplaced(const uint32_t var) const;
        bool isReplaced(const Lit lit) const;
        bool isReplaced_fast(const uint32_t var) const;
        bool isReplaced_fast(const Lit lit) const;

        size_t getNumTrees() const;
        void set_sub_var_during_solution_extension(uint32_t var, uint32_t sub_var);
        void checkUnsetSanity();

        bool replace_set(vector<ClOffset>& cs);
        void attach_delayed_attach();
        void update_all_vardata_activities();
        void update_vardata_and_activities(
            const uint32_t orig
            , const uint32_t replaced
        );
        bool enqueueDelayedEnqueue();

        //Helpers for replace()
        void replaceChecks(const uint32_t var1, const uint32_t var2) const;
        bool handleAlreadyReplaced(const Lit lit1, const Lit lit2);
        bool replace_vars_already_set(
            const Lit lit1
            , const lbool val1
            , const Lit lit2
            , const lbool val2
        );
        bool handleOneSet(
            const Lit lit1
            , const lbool val1
            , const Lit lit2
            , const lbool val2
        );

        //Temporary used in replaceImplicit
        vector<BinaryClause> delayed_attach_bin;
        bool replaceImplicit();
        struct ImplicitTmpStats
        {
            ImplicitTmpStats() :
                removedRedBin(0)
                , removedIrredBin(0)
            {
            }

            void remove(const Watched& ws)
            {
                if (ws.isBin()) {
                    if (ws.red()) {
                        removedRedBin++;
                    } else {
                        removedIrredBin++;
                    }
                } else {
                    assert(false);
                }
            }

            void clear()
            {
                *this = ImplicitTmpStats();
            }

            size_t removedRedBin;
            size_t removedIrredBin;
        };
        ImplicitTmpStats impl_tmp_stats;
        void updateBin(
            Watched* i
            , Watched*& j
            , const Lit origLit1
            , const Lit origLit2
            , Lit lit1
            , Lit lit2
        );
        void newBinClause(
            Lit origLit1
            , Lit origLit2
            , Lit origLit3
            , Lit lit1
            , Lit lit2
            , bool red
        );
        void updateStatsFromImplStats();

        bool handleUpdatedClause(Clause& c, const Lit origLit1, const Lit origLit2);

         //While replacing the implicit clauses we cannot enqeue
        vector<Lit> delayedEnqueue;
        bool update_table_and_reversetable(const Lit lit1, const Lit lit2);
        void setAllThatPointsHereTo(const uint32_t var, const Lit lit);

        //Mapping tables
        vector<Lit> table; ///<Stores which variables have been replaced by which literals. Index by: table[VAR]
        map<uint32_t, vector<uint32_t> > reverseTable; ///<mapping of variable to set of variables it replaces

        //Stats
        void printReplaceStats() const;
        uint64_t replacedVars = 0; ///<Num vars replaced during var-replacement
        uint64_t lastReplacedVars = 0;
        Stats runStats;
        Stats globalStats;
};

inline size_t VarReplacer::get_num_replaced_vars() const
{
    return replacedVars;
}

inline bool VarReplacer::isReplaced(const uint32_t var) const
{
    return get_var_replaced_with(var) != var;
}

inline bool VarReplacer::isReplaced_fast(const uint32_t var) const
{
    return get_var_replaced_with_fast(var) != var;
}

inline uint32_t VarReplacer::get_var_replaced_with(const Lit lit) const
{
    return get_var_replaced_with(lit.var());
}

inline bool VarReplacer::isReplaced(const Lit lit) const
{
    return isReplaced(lit.var());
}

inline bool VarReplacer::isReplaced_fast(const Lit lit) const
{
    return isReplaced_fast(lit.var());
}

inline size_t VarReplacer::getNumTrees() const
{
    return reverseTable.size();
}

inline vector<uint32_t> VarReplacer::get_vars_replacing_others() const
{
    vector<uint32_t> replacingVars;
    for(const auto& it: reverseTable) {
        replacingVars.push_back(it.first);
    }
    return replacingVars;
}

inline bool VarReplacer::var_is_replacing(const uint32_t var)
{
    auto it = reverseTable.find(var);
    return it != reverseTable.end();
}

inline const VarReplacer::Stats& VarReplacer::get_stats() const
{
    return globalStats;
}

inline const SCCFinder* VarReplacer::get_scc_finder() const
{
    return scc_finder;
}

inline Lit VarReplacer::get_lit_replaced_with_outer(Lit lit) const
{
    Lit lit2 = table[lit.var()] ^ lit.sign();
    return lit2;
}

inline uint32_t VarReplacer::get_var_replaced_with_outer(uint32_t var) const
{
    return table[var].var();
}

} //end namespace

#endif //VARREPLACER_H

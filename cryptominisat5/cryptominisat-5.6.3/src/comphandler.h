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

#ifndef PARTHANDLER_H
#define PARTHANDLER_H

#include "solvertypes.h"
#include "cloffset.h"
#include <map>
#include <vector>

namespace CMSat {

using std::map;
using std::vector;
using std::pair;

class SATSolver;
class Solver;
class CompFinder;
class Watched;

/**
@brief Disconnected components are treated here

Uses CompFinder to find disconnected components and treats them using
subsolvers. The solutions (if SAT) are aggregated, and at then end, the
solution is extended with the sub-solutions, and the removed clauses are
added back to the problem.
*/
class CompHandler
{
    public:
        explicit CompHandler(Solver* solver);
        ~CompHandler();

        struct RemovedClauses {
            vector<Lit> lits;
            vector<uint32_t> sizes;
        };

        bool handle();
        const vector<lbool>& getSavedState();
        void new_var(const uint32_t orig_outer);
        void new_vars(const size_t n);
        void save_on_var_memory();
        void addSavedState(vector<lbool>& solution);
        void readdRemovedClauses();
        const RemovedClauses& getRemovedClauses() const;
        void dump_removed_clauses(std::ostream* outfile) const;
        size_t get_num_vars_removed() const;
        size_t get_num_components_solved() const;
        size_t mem_used() const;

    private:
        struct sort_pred {
            bool operator()(
                const std::pair<int,int> &left
                , const std::pair<int,int> &right
            ) {
                return left.second < right.second;
            }
        };
        bool assumpsInsideComponent(const vector<uint32_t>& vars);
        void move_decision_level_zero_vars_here(
            const SATSolver* newSolver
        );
        void save_solution_to_savedstate(
            const SATSolver* newSolver
            , const vector<uint32_t>& vars
            , const uint32_t comp
        );
        void check_solution_is_unassigned_in_main_solver(
            const SATSolver* newSolver
            , const vector<uint32_t>& vars
        );
        void check_local_vardata_sanity();
        bool try_to_solve_component(
            const uint32_t comp_at
            , const uint32_t comp
            , const vector<uint32_t>& vars
            , const size_t num_comps
        );
        bool solve_component(
            const uint32_t comp_at
            , const uint32_t comp
            , const vector<uint32_t>& vars_orig
            , const size_t num_comps
        );
        vector<pair<uint32_t, uint32_t> > get_component_sizes() const;

        SolverConf configureNewSolver(
            const size_t numVars
        ) const;

        void moveVariablesBetweenSolvers(
            SATSolver* newSolver
            , const vector<uint32_t>& vars
            , const uint32_t comp
        );

        //For moving clauses
        void moveClausesImplicit(
            SATSolver* newSolver
            , const uint32_t comp
            , const vector<uint32_t>& vars
        );
        void moveClausesLong(
            vector<ClOffset>& cs
            , SATSolver* newSolver
            , const uint32_t comp
        );
        void move_binary_clause(
            SATSolver* newSolver
            , const uint32_t comp
            ,  Watched *i
            , const Lit lit
        );
        void remove_bin_except_for_lit1(const Lit lit, const Lit lit2);

        Solver* solver;
        CompFinder* compFinder;

        ///The solutions that have been found by the comps
        vector<lbool> savedState;

        //Re-numbering
        void createRenumbering(const vector<uint32_t>& vars);
        vector<uint32_t> useless; //temporary
        vector<uint32_t> smallsolver_to_bigsolver;
        vector<uint32_t> bigsolver_to_smallsolver;

        Lit upd_bigsolver_to_smallsolver(const Lit lit) const
        {
            return Lit(upd_bigsolver_to_smallsolver(lit.var()), lit.sign());
        }

        uint32_t upd_bigsolver_to_smallsolver(const uint32_t var) const
        {
            return bigsolver_to_smallsolver[var];
        }

        //Saving clauses
        template<class T>
        void saveClause(const T& lits);
        RemovedClauses removedClauses;
        size_t num_vars_removed = 0;
        size_t components_solved = 0;

        //Clauses that have been moved to other comps
        //vector<ClOffset> clausesRemoved;
        //vector<pair<Lit, Lit> > binClausesRemoved;

        uint32_t numRemovedHalfIrred = 0;
        uint32_t numRemovedHalfRed = 0;
        vector<Lit> tmp_lits;
};

/**
@brief Returns the saved state of a variable
*/
inline const vector<lbool>& CompHandler::getSavedState()
{
    return savedState;
}

inline const CompHandler::RemovedClauses& CompHandler::getRemovedClauses() const
{
    return removedClauses;
}

inline size_t CompHandler::get_num_vars_removed() const
{
    return num_vars_removed;
}

inline size_t CompHandler::get_num_components_solved() const
{
    return components_solved;
}

} //end of namespace

#endif //PARTHANDLER_H

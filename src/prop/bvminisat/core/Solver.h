/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef BVMinisat_Solver_h
#define BVMinisat_Solver_h

#include <vector>

#include "base/check.h"
#include "context/context.h"
#include "proof/clause_id.h"
#include "prop/bvminisat/core/SolverTypes.h"
#include "prop/bvminisat/mtl/Alg.h"
#include "prop/bvminisat/mtl/Heap.h"
#include "prop/bvminisat/mtl/Vec.h"
#include "prop/bvminisat/utils/Options.h"
#include "util/resource_manager.h"

namespace cvc5 {

namespace BVMinisat {
class Solver;
}

namespace BVMinisat {

/** Interface for minisat callbacks */
class Notify {

public:

  virtual ~Notify() {}

  /**
   * If the notify returns false, the solver will break out of whatever it's currently doing
   * with an "unknown" answer.
   */
  virtual bool notify(Lit lit) = 0;

  /**
   * Notify about a new learnt clause with marked literals only.
   */
  virtual void notify(vec<Lit>& learnt) = 0;

  virtual void spendResource(Resource r) = 0;
  virtual void safePoint(Resource r) = 0;
};

//=================================================================================================
// Solver -- the main class:
class Solver {
public:
    typedef Var TVar;
    typedef Lit TLit;
    typedef Clause TClause;
    typedef CRef TCRef;
    typedef vec<Lit> TLitVec;

    static CRef TCRef_Undef;
    static CRef TCRef_Lazy;
private:
    /** To notify */
    Notify* d_notify;

    /** cvc5 context */
    cvc5::context::Context* c;

    /** True constant */
    Var varTrue;

    /** False constant */
    Var varFalse;

public:

    // Constructor/Destructor:
    //
 Solver(cvc5::context::Context* c);
 virtual ~Solver();

 void setNotify(Notify* toNotify);

 // Problem specification:
 //
 Var newVar(bool polarity = true,
            bool dvar = true);  // Add a new variable with parameters specifying
                                // variable mode.
 Var trueVar() const { return varTrue; }
 Var falseVar() const { return varFalse; }

 bool addClause(const vec<Lit>& ps,
                ClauseId& id);  // Add a clause to the solver.
 bool addEmptyClause();         // Add the empty clause, making the solver
                                // contradictory.
 bool addClause(Lit p, ClauseId& id);  // Add a unit clause to the solver.
 bool addClause(Lit p,
                Lit q,
                ClauseId& id);  // Add a binary clause to the solver.
 bool addClause(Lit p,
                Lit q,
                Lit r,
                ClauseId& id);  // Add a ternary clause to the solver.
 bool addClause_(
     vec<Lit>& ps,
     ClauseId& id);  // Add a clause to the solver without making superflous
                     // internal copy. Will change the passed vector 'ps'.

 // Solving:
 //
 bool simplify();                       // Removes already satisfied clauses.
 lbool solve(const vec<Lit>& assumps);  // Search for a model that respects a
                                        // given set of assumptions.
 lbool solveLimited(
     const vec<Lit>& assumps);  // Search for a model that respects a given set
                                // of assumptions (With resource constraints).
 lbool solve();                 // Search without assumptions.
 lbool solve(Lit p);  // Search for a model that respects a single assumption.
 lbool solve(Lit p,
             Lit q);  // Search for a model that respects two assumptions.
 lbool solve(Lit p,
             Lit q,
             Lit r);  // Search for a model that respects three assumptions.
 bool okay() const;   // FALSE means solver is in a conflicting state
 lbool assertAssumption(
     Lit p,
     bool propagate);  // Assert a new assumption, start BCP if propagate = true
 lbool propagateAssumptions();  // Do BCP over asserted assumptions
 void popAssumption();          // Pop an assumption

 void toDimacs(FILE* f,
               const vec<Lit>& assumps);  // Write CNF to file in DIMACS-format.
 void toDimacs(const char* file, const vec<Lit>& assumps);
 void toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max);

 // Convenience versions of 'toDimacs()':
 void toDimacs(const char* file);
 void toDimacs(const char* file, Lit p);
 void toDimacs(const char* file, Lit p, Lit q);
 void toDimacs(const char* file, Lit p, Lit q, Lit r);

 // Variable mode:
 //
 void setPolarity(
     Var v, bool b);  // Declare which polarity the decision heuristic should
                      // use for a variable. Requires mode 'polarity_user'.
 void setDecisionVar(Var v,
                     bool b);  // Declare if a variable should be eligible for
                               // selection in the decision heuristic.

 // Read state:
 //
 lbool value(Var x) const;  // The current value of a variable.
 lbool value(Lit p) const;  // The current value of a literal.
 lbool modelValue(
     Var x) const;  // The value of a variable in the last model. The last call
                    // to solve must have been satisfiable.
 lbool modelValue(
     Lit p) const;  // The value of a literal in the last model. The last call
                    // to solve must have been satisfiable.
 int nAssigns() const;  // The current number of assigned literals.
 int nClauses() const;  // The current number of original clauses.
 int nLearnts() const;  // The current number of learnt clauses.
 int nVars() const;     // The current number of variables.
 int nFreeVars() const;

 // Resource contraints:
 //
 void setConfBudget(int64_t x);
 void setPropBudget(int64_t x);
 void budgetOff();
 void interrupt();  // Trigger a (potentially asynchronous) interruption of the
                    // solver.
 void clearInterrupt();  // Clear interrupt indicator flag.

 // Memory managment:
 //
 virtual void garbageCollect();
 void checkGarbage(double gf);
 void checkGarbage();

 // Extra results: (read-only member variable)
 //
 vec<lbool> model;  // If problem is satisfiable, this vector contains the model
                    // (if any).
 vec<Lit> conflict;  // If problem is unsatisfiable (possibly under
                     // assumptions), this vector represent the final conflict
                     // clause expressed in the assumptions.

 // Mode of operation:
 //
 int verbosity;
 double var_decay;
 double clause_decay;
 double random_var_freq;
 double random_seed;
 bool luby_restart;
 int ccmin_mode;    // Controls conflict clause minimization (0=none, 1=basic,
                    // 2=deep).
 int phase_saving;  // Controls the level of phase saving (0=none, 1=limited,
                    // 2=full).
 bool rnd_pol;      // Use random polarities for branching heuristics.
 bool
     rnd_init_act;  // Initialize variable activities with a small random value.
 double garbage_frac;  // The fraction of wasted memory allowed before a garbage
                       // collection is triggered.

 int restart_first;   // The initial restart limit. (default 100)
 double restart_inc;  // The factor with which the restart limit is multiplied
                      // in each restart.                    (default 1.5)
 double
     learntsize_factor;  // The intitial limit for learnt clauses is a factor of
                         // the original clauses.                (default 1 / 3)
 double learntsize_inc;  // The limit for learnt clauses is multiplied with this
                         // factor each restart.                 (default 1.1)

 int learntsize_adjust_start_confl;
 double learntsize_adjust_inc;

 // Statistics: (read-only member variable)
 //
 int64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
 int64_t dec_vars, clauses_literals, learnts_literals, max_literals,
     tot_literals;

 // Bitvector Propagations
 //

 void addMarkerLiteral(Var var);

 bool need_to_propagate;  // true if we added new clauses, set to true in
                          // propagation
 bool only_bcp;  // solving mode in which only boolean constraint propagation is
                 // done
 void setOnlyBCP(bool val) { only_bcp = val; }
 void explain(Lit l, std::vector<Lit>& explanation);

protected:
 // has a clause been added
 bool clause_added;

 // Helper structures:
 //
 struct VarData
 {
   CRef reason;
   int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           marker;           // Is the variable a marker literal
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.

    enum UIP {
      UIP_FIRST,
      UIP_LAST
    };

    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel, UIP uip = UIP_FIRST);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    void     analyzeFinal2(Lit p, CRef confl_clause, vec<Lit>& out_conflict);
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts, UIP uip = UIP_FIRST);                // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool withinBudget(Resource r) const;

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }

  // Less than for literals in an added clause when proofs are on.
  struct assign_lt {
    Solver& d_solver;
    assign_lt(Solver& solver) : d_solver(solver) {}
    bool operator () (Lit x, Lit y) {
      lbool x_value = d_solver.value(x);
      lbool y_value = d_solver.value(y);
      // Two unassigned literals are sorted arbitrarily
      if (x_value == l_Undef && y_value == l_Undef) {
        return x < y;
      }
      // Unassigned literals are put to front
      if (x_value == l_Undef) return true;
      if (y_value == l_Undef) return false;
      // Literals of the same value are sorted by decreasing levels
      if (x_value == y_value) {
        return d_solver.level(var(x)) > d_solver.level(var(y));
      } else {
        // True literals go up front
        if (x_value == l_True) {
          return true;
        } else {
          return false;
        }
      }
    }
  };

};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].reason;
}
inline int Solver::level(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].level;
}

inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity(Clause& clause)
{
  if ((clause.activity() += cla_inc) > 1e20)
  {
    // Rescale:
    for (int i = 0; i < learnts.size(); i++) ca[learnts[i]].activity() *= 1e-20;
    cla_inc *= 1e-20;
  }
}

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps, ClauseId& id)    { ps.copyTo(add_tmp); return addClause_(add_tmp, id); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); ClauseId tmp; return addClause_(add_tmp, tmp); }
inline bool     Solver::addClause       (Lit p, ClauseId& id)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp, id); }
inline bool     Solver::addClause       (Lit p, Lit q, ClauseId& id)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp, id); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r, ClauseId& id)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp, id); }
inline bool Solver::locked(const Clause& clause) const
{
  return value(clause[0]) == l_True && reason(var(clause[0])) != CRef_Undef
         && ca.lea(reason(var(clause[0]))) == &clause;
}
inline void     Solver::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void Solver::setDecisionVar(Var v, bool b)
{
  if (b && !decision[v])
    dec_vars++;
  else if (!b && decision[v])
    dec_vars--;

  decision[v] = b;
  insertVarOrder(v);
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }

inline lbool     Solver::solve         ()                    { budgetOff(); return solve_(); }
inline lbool     Solver::solve         (Lit p)               { budgetOff(); assumptions.push(p); return solve_(); }
inline lbool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.push(p); assumptions.push(q); return solve_(); }
inline lbool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_(); }
inline lbool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_(); }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }


//=================================================================================================
// Debug etc:


//=================================================================================================
}  // namespace BVMinisat
}  // namespace cvc5

#endif

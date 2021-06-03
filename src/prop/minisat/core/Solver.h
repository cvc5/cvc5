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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include <iosfwd>

#include "base/check.h"
#include "base/output.h"
#include "context/context.h"
#include "cvc5_private.h"
#include "proof/clause_id.h"
#include "proof/proof_node_manager.h"
#include "prop/minisat/core/SolverTypes.h"
#include "prop/minisat/mtl/Alg.h"
#include "prop/minisat/mtl/Heap.h"
#include "prop/minisat/mtl/Vec.h"
#include "prop/minisat/utils/Options.h"
#include "prop/sat_proof_manager.h"
#include "theory/theory.h"
#include "util/resource_manager.h"

namespace cvc5 {

namespace prop {
class PropEngine;
class TheoryProxy;
}  // namespace prop
}  // namespace cvc5

namespace cvc5 {
namespace Minisat {

//=================================================================================================
// Solver -- the main class:

class Solver {
  /** The only two cvc5 entry points to the private solver data */
  friend class cvc5::prop::PropEngine;
  friend class cvc5::prop::TheoryProxy;
  friend class cvc5::prop::SatProofManager;

 public:
  static CRef TCRef_Undef;
  static CRef TCRef_Lazy;

  typedef Var TVar;
  typedef Lit TLit;
  typedef Clause TClause;
  typedef CRef TCRef;
  typedef vec<Lit> TLitVec;

 protected:
  /** The pointer to the proxy that provides interfaces to the SMT engine */
  cvc5::prop::TheoryProxy* d_proxy;

  /** The context from the SMT solver */
  cvc5::context::Context* d_context;

  /** The current assertion level (user) */
  int assertionLevel;

  /** Variable representing true */
  Var varTrue;

  /** Variable representing false */
  Var varFalse;

  /** The resolution proof manager */
  std::unique_ptr<cvc5::prop::SatProofManager> d_pfManager;

 public:
  /** Returns the current user assertion level */
  int getAssertionLevel() const { return assertionLevel; }

 protected:
  /** Do we allow incremental solving */
  bool d_enable_incremental;

  /** Literals propagated by lemmas */
  vec<vec<Lit> > lemmas;

  /** Is the lemma removable */
  vec<bool> lemmas_removable;

  /** Do a another check if FULL_EFFORT was the last one */
  bool recheck;

  /** Shrink 'cs' to contain only clauses below given level */
  void removeClausesAboveLevel(vec<CRef>& cs, int level);

  /** True if we are currently solving. */
  bool minisat_busy;

  // Information about registration of variables
  struct VarIntroInfo
  {
    Var d_var;
    int d_level;
    VarIntroInfo(Var var, int level) : d_var(var), d_level(level) {}
  };

  /** Variables to re-register with theory solvers on backtracks */
  vec<VarIntroInfo> variables_to_register;

  /** Keep only newSize variables */
  void resizeVars(int newSize);

public:

    // Constructor/Destructor:
    //
 Solver(cvc5::prop::TheoryProxy* proxy,
        cvc5::context::Context* context,
        cvc5::context::UserContext* userContext,
        ProofNodeManager* pnm,
        bool enableIncremental = false);
 virtual ~Solver();

 // Problem specification:
 //
 Var newVar(bool polarity = true,
            bool dvar = true,
            bool isTheoryAtom = false,
            bool preRegister = false,
            bool canErase = true);  // Add a new variable with parameters
                                    // specifying variable mode.
 Var trueVar() const { return varTrue; }
 Var falseVar() const { return varFalse; }

 /** Retrive the SAT proof manager */
 cvc5::prop::SatProofManager* getProofManager();

 /** Retrive the refutation proof */
 std::shared_ptr<ProofNode> getProof();

 /** Is proof enabled? */
 bool isProofEnabled() const;

 /**
  * Checks whether we need a proof.
  *
  * SAT proofs are not required for assumption-based unsat cores.
  */
 bool needProof() const;

 // Less than for literals in a lemma
 struct lemma_lt
 {
   Solver& d_solver;
   lemma_lt(Solver& solver) : d_solver(solver) {}
   bool operator()(Lit x, Lit y)
   {
     lbool x_value = d_solver.value(x);
     lbool y_value = d_solver.value(y);
     // Two unassigned literals are sorted arbitrarily
     if (x_value == l_Undef && y_value == l_Undef)
     {
       return x < y;
     }
     // Unassigned literals are put to front
     if (x_value == l_Undef) return true;
     if (y_value == l_Undef) return false;
     // Literals of the same value are sorted by decreasing levels
     if (x_value == y_value)
     {
       return d_solver.trail_index(var(x)) > d_solver.trail_index(var(y));
     }
     else
     {
       // True literals go up front
       if (x_value == l_True)
       {
         return true;
       }
       else
       {
         return false;
       }
     }
   }
 };

 // cvc5 context push/pop
 void push();
 void pop();

 /*
  * Reset the decisions in the DPLL(T) SAT solver at the current assertion
  * level.
  */
 void resetTrail();
 // addClause returns the ClauseId corresponding to the clause added in the
 // reference parameter id.
 bool addClause(const vec<Lit>& ps,
                bool removable,
                ClauseId& id);  // Add a clause to the solver.
 bool addEmptyClause(
     bool removable);  // Add the empty clause, making the solver contradictory.
 bool addClause(Lit p,
                bool removable,
                ClauseId& id);  // Add a unit clause to the solver.
 bool addClause(Lit p,
                Lit q,
                bool removable,
                ClauseId& id);  // Add a binary clause to the solver.
 bool addClause(Lit p,
                Lit q,
                Lit r,
                bool removable,
                ClauseId& id);  // Add a ternary clause to the solver.
 bool addClause_(
     vec<Lit>& ps,
     bool removable,
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

 void toDimacs();
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
 void freezePolarity(
     Var v,
     bool b);  // Declare which polarity the decision heuristic MUST ALWAYS use
               // for a variable. Requires mode 'polarity_user'.
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
 bool isDecision(Var x) const;  // is the given var a decision?

 // Debugging SMT explanations
 //
 bool properExplanation(Lit l, Lit expl)
     const;  // returns true if expl can be used to explain l---i.e., both
             // assigned and trail_index(expl) < trail_index(l)

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
 vec<Lit> d_conflict;  // If problem is unsatisfiable (possibly under
                       // assumptions), this vector represent the final
                       // conflict clause expressed in the assumptions.

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
 int64_t solves, starts, decisions, rnd_decisions, propagations, conflicts,
     resources_consumed;
 int64_t dec_vars, clauses_literals, learnts_literals, max_literals,
     tot_literals;

protected:

    // Helper structures:
    //
    struct VarData {
      // Reason for the literal being in the trail
      CRef d_reason;
      // Sat level when the literal was added to the trail
      int d_level;
      // User level when the literal was added to the trail
      int d_user_level;
      // User level at which this literal was introduced
      int d_intro_level;
      // The index in the trail
      int d_trail_index;

      VarData(CRef reason,
              int level,
              int user_level,
              int intro_level,
              int trail_index)
          : d_reason(reason),
            d_level(level),
            d_user_level(user_level),
            d_intro_level(intro_level),
            d_trail_index(trail_index)
      {}
    };

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
    bool                ok;                 // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses_persistent; // List of problem clauses.
    vec<CRef>           clauses_removable;  // List of learnt clauses.
    double              cla_inc;            // Amount to bump next clause with.
    vec<double>         activity;           // A heuristic measurement of the activity of a variable.
    double              var_inc;            // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches;            // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;            // The current assignments.
    vec<int>            assigns_lim;        // The size by levels of the current assignment
    vec<char>           polarity;           // The preferred polarity of each variable (bit 0) and whether it's locked (bit 1).
    vec<char>           decision;           // Declares if a variable is eligible for selection in the decision heuristic.
    vec<int>            flipped;            // Which trail_lim decisions have been flipped in this context.
    vec<Lit>            trail;              // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;          // Separator indices for different decision levels in 'trail'.
    vec<bool>           trail_ok;           // Stack of "whether we're in conflict" flags.
    vec<VarData>        vardata;            // Stores reason and level for each variable.
    int                 qhead;              // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;     // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;       // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;        // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;         // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;  // Set by 'search()'.
    bool                remove_satisfied;   // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca;

    // cvc5 Stuff
    /**
     * A vector determining whether each variable represents a theory atom.
     * More generally, this value is true for any literal that the theory proxy
     * should be notified about when asserted.
     */
    vec<bool> theory;

    enum TheoryCheckType {
      // Quick check, but don't perform theory reasoning
      CHECK_WITHOUT_THEORY,
      // Check and perform theory reasoning
      CHECK_WITH_THEORY,
      // The SAT abstraction of the problem is satisfiable, perform a full theory check
      CHECK_FINAL,
      // Perform a full theory check even if not done with everything
      CHECK_FINAL_FAKE
    };

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
    bool     theoryConflict;                                                           // Was the last conflict a theory conflict
    CRef     propagate        (TheoryCheckType type);                                  // Perform Boolean and Theory. Returns possibly conflicting clause.
    CRef     propagateBool    ();                                                      // Perform Boolean propagation. Returns possibly conflicting clause.
    void     propagateTheory  ();                                                      // Perform Theory propagation.
    void theoryCheck(
        cvc5::theory::Theory::Effort
            effort);  // Perform a theory satisfiability check. Adds lemmas.
    CRef     updateLemmas     ();                                                      // Add the lemmas, backtraking if necessary and return a conflict if there is one
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    int      analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()') - true if p is redundant
    lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
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
    CRef     reason           (Var x); // Get the reason of the variable (non const as it might create the explanation on the fly)
    bool     hasReasonClause  (Var x) const; // Does the variable have a reason
    bool     isPropagated     (Var x) const; // Does the variable have a propagated variables
    bool     isPropagatedBy   (Var x, const Clause& c) const; // Is the value of the variable propagated by the clause Clause C

    int      trail_index      (Var x) const; // Index in the trail
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
public:
    int      level            (Var x) const;
    int      user_level       (Var x) const; // User level at which this variable was asserted
    int      intro_level      (Var x) const; // User level at which this variable was created
    bool     withinBudget     (uint64_t amount)      const;
    bool withinBudget(Resource r) const;

   protected:
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

};



//=================================================================================================
// Implementation of inline methods:

inline bool Solver::hasReasonClause(Var x) const
{
  return vardata[x].d_reason != CRef_Undef && vardata[x].d_reason != CRef_Lazy;
}

inline bool Solver::isPropagated(Var x) const
{
  return vardata[x].d_reason != CRef_Undef;
}

inline bool Solver::isPropagatedBy(Var x, const Clause& c) const
{
  return vardata[x].d_reason != CRef_Undef && vardata[x].d_reason != CRef_Lazy
         && ca.lea(vardata[var(c[0])].d_reason) == &c;
}

inline bool Solver::isDecision(Var x) const
{
  Debug("minisat") << "var " << x << " is a decision iff "
                   << (vardata[x].d_reason == CRef_Undef) << " && " << level(x)
                   << " > 0" << std::endl;
  return vardata[x].d_reason == CRef_Undef && level(x) > 0;
}

inline int Solver::level(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].d_level;
}

inline int Solver::user_level(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].d_user_level;
}

inline int Solver::intro_level(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].d_intro_level;
}

inline int Solver::trail_index(Var x) const
{
  Assert(x < vardata.size());
  return vardata[x].d_trail_index;
}

inline void Solver::insertVarOrder(Var x) {
  Assert(x < vardata.size());
  if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x);
}

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
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < clauses_removable.size(); i++)
                ca[clauses_removable[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps, bool removable, ClauseId& id)
                                                                { ps.copyTo(add_tmp); return addClause_(add_tmp, removable, id); }
inline bool     Solver::addEmptyClause  (bool removable)        { add_tmp.clear(); ClauseId tmp; return addClause_(add_tmp, removable, tmp); }
inline bool     Solver::addClause       (Lit p, bool removable, ClauseId& id)
                                                                { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp, removable, id); }
inline bool     Solver::addClause       (Lit p, Lit q, bool removable, ClauseId& id)
                                                                { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp, removable, id); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r, bool removable, ClauseId& id)
                                                                { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp, removable, id); }
inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && isPropagatedBy(var(c[0]), c); }
inline void Solver::newDecisionLevel()
{
  trail_lim.push(trail.size());
  flipped.push(false);
  d_context->push();
}

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool Solver::value(Var x) const
{
  Assert(x < nVars());
  return assigns[x];
}
inline lbool Solver::value(Lit p) const
{
  Assert(var(p) < nVars());
  return assigns[var(p)] ^ sign(p);
}
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses_persistent.size(); }
inline int      Solver::nLearnts      ()      const   { return clauses_removable.size(); }
inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline bool     Solver::properExplanation(Lit l, Lit expl) const { return value(l) == l_True && value(expl) == l_True && trail_index(var(expl)) < trail_index(var(l)); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver::freezePolarity(Var v, bool b) { polarity[v] = int(b) | 0x2; }
inline void     Solver::setDecisionVar(Var v, bool b)
{
    if      ( b && !decision[v] ) dec_vars++;
    else if (!b &&  decision[v] ) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}

inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }

inline lbool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_(); }
inline lbool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_(); }
inline lbool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_(); }
inline lbool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_(); }
inline lbool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_(); }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     () { vec<Lit> as; toDimacs(stdout, as); }
inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }



//=================================================================================================
// Debug etc:


//=================================================================================================
}  // namespace Minisat
}  // namespace cvc5

#endif

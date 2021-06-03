/************************************************************************************[SimpSolver.h]
Copyright (c) 2006,      Niklas Een, Niklas Sorensson
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

#ifndef BVMinisat_SimpSolver_h
#define BVMinisat_SimpSolver_h

#include "base/check.h"
#include "proof/clause_id.h"
#include "prop/bvminisat/core/Solver.h"
#include "prop/bvminisat/mtl/Queue.h"

namespace cvc5 {

namespace context {
class Context;
}

namespace BVMinisat {

//=================================================================================================


class SimpSolver : public Solver {
 public:
    // Constructor/Destructor:
    //
  SimpSolver(cvc5::context::Context* context);
  ~SimpSolver();

  // Problem specification:
  //
  Var newVar(bool polarity = true, bool dvar = true, bool freeze = false);
  bool addClause(const vec<Lit>& ps, ClauseId& id);
  bool addEmptyClause();                // Add the empty clause to the solver.
  bool addClause(Lit p, ClauseId& id);  // Add a unit clause to the solver.
  bool addClause(Lit p,
                 Lit q,
                 ClauseId& id);  // Add a binary clause to the solver.
  bool addClause(Lit p,
                 Lit q,
                 Lit r,
                 ClauseId& id);  // Add a ternary clause to the solver.
  bool addClause_(vec<Lit>& ps, ClauseId& id);
  bool substitute(Var v, Lit x);  // Replace all occurrences of v with x (may
                                  // cause a contradiction).

  // Variable mode:
  //
  void setFrozen(Var v,
                 bool b);  // If a variable is frozen it will not be eliminated.
  bool isEliminated(Var v) const;

  // Solving:
  //
  lbool solve(const vec<Lit>& assumps,
              bool do_simp = true,
              bool turn_off_simp = false);
  lbool solveLimited(const vec<Lit>& assumps,
                     bool do_simp = true,
                     bool turn_off_simp = false);
  lbool solveLimited(bool do_simp = true, bool turn_off_simp = false);
  lbool solve(bool do_simp = true, bool turn_off_simp = false);
  lbool solve(Lit p, bool do_simp = true, bool turn_off_simp = false);
  lbool solve(Lit p, Lit q, bool do_simp = true, bool turn_off_simp = false);
  lbool solve(
      Lit p, Lit q, Lit r, bool do_simp = true, bool turn_off_simp = false);
  bool eliminate(bool turn_off_elim = false);  // Perform variable elimination
                                               // based simplification.

  // Memory managment:
  //
  void garbageCollect() override;

  // Generate a (possibly simplified) DIMACS file:
  //
#if 0
    void    toDimacs  (const char* file, const vec<Lit>& assumps);
    void    toDimacs  (const char* file);
    void    toDimacs  (const char* file, Lit p);
    void    toDimacs  (const char* file, Lit p, Lit q);
    void    toDimacs  (const char* file, Lit p, Lit q, Lit r);
#endif

    // Mode of operation:
    //
    int     grow;              // Allow a variable elimination step to grow by a number of clauses (default to zero).
    int     clause_lim;        // Variables are not eliminated if it produces a resolvent with a length above this limit.
                               // -1 means no limit.
    int     subsumption_lim;   // Do not check if subsumption against a clause larger than this. -1 means no limit.
    double  simp_garbage_frac; // A different limit for when to issue a GC during simplification (Also see 'garbage_frac').

    bool    use_asymm;         // Shrink clauses by asymmetric branching.
    bool    use_rcheck;        // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    bool    use_elim;          // Perform variable elimination.

    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int64_t eliminated_vars;
    //    cvc5::TimerStat total_eliminate_time;

   protected:

    // Helper structures:
    //
    struct ElimLt {
        const vec<int>& n_occ;
        explicit ElimLt(const vec<int>& no) : n_occ(no) {}

        // TODO: are 64-bit operations here noticably bad on 32-bit platforms? Could use a saturating
        // 32-bit implementation instead then, but this will have to do for now.
        uint64_t cost  (Var x)        const { return (uint64_t)n_occ[toInt(mkLit(x))] * (uint64_t)n_occ[toInt(~mkLit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); }
        
        // TODO: investigate this order alternative more.
        // bool operator()(Var x, Var y) const { 
        //     int c_x = cost(x);
        //     int c_y = cost(y);
        //     return c_x < c_y || c_x == c_y && x < y; }
    };

    struct ClauseDeleted {
        const ClauseAllocator& ca;
        explicit ClauseDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const CRef& cr) const { return ca[cr].mark() == 1; } };

    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    vec<uint32_t>       elimclauses;
    vec<char>           touched;
    OccLists<Var, vec<CRef>, ClauseDeleted>
                        occurs;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    Queue<CRef>         subsumption_queue;
    vec<char>           frozen;
    vec<char>           eliminated;
    int                 bwdsub_assigns;
    int                 n_touched;

    // Temporaries:
    //
    CRef                bwdsub_tmpunit;

    // Main internal methods:
    //
    lbool         solve_                   (bool do_simp = true, bool turn_off_simp = false);
    bool          asymm                    (Var v, CRef cr);
    bool          asymmVar                 (Var v);
    void          updateElimHeap           (Var v);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, int& size);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v);
    void          extendModel              ();

    void          removeClause             (CRef cr);
    bool          strengthenClause         (CRef cr, Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const vec<Lit>& c);
    void          relocAll                 (ClauseAllocator& to);
};


//=================================================================================================
// Implementation of inline methods:


inline bool SimpSolver::isEliminated (Var v) const { return eliminated[v]; }
inline void SimpSolver::updateElimHeap(Var v) {
  Assert(use_simplification);
  // if (!frozen[v] && !isEliminated(v) && value(v) == l_Undef)
  if (elim_heap.inHeap(v)
      || (!frozen[v] && !isEliminated(v) && value(v) == l_Undef))
    elim_heap.update(v);
}

inline bool SimpSolver::addClause    (const vec<Lit>& ps, ClauseId& id)    { ps.copyTo(add_tmp); return addClause_(add_tmp, id); }
inline bool SimpSolver::addEmptyClause()                     { add_tmp.clear(); ClauseId id; return addClause_(add_tmp, id); }
inline bool SimpSolver::addClause    (Lit p, ClauseId& id)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp, id); }
inline bool SimpSolver::addClause    (Lit p, Lit q, ClauseId& id)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp, id); }
inline bool SimpSolver::addClause    (Lit p, Lit q, Lit r, ClauseId& id)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp, id); }
inline void SimpSolver::setFrozen    (Var v, bool b) { frozen[v] = (char)b; if (use_simplification && !b) { updateElimHeap(v); } }

inline lbool SimpSolver::solve        (                     bool do_simp, bool turn_off_simp)  {
  budgetOff();
  return solve_(do_simp, turn_off_simp);
 }
inline lbool SimpSolver::solve        (Lit p       ,        bool do_simp, bool turn_off_simp)  {
  budgetOff();
  assumptions.push(p);
  return solve_(do_simp, turn_off_simp);
 }
inline lbool SimpSolver::solve        (Lit p, Lit q,        bool do_simp, bool turn_off_simp)  {
  budgetOff();
  assumptions.push(p);
  assumptions.push(q);
  return solve_(do_simp, turn_off_simp);
 }
inline lbool SimpSolver::solve        (Lit p, Lit q, Lit r, bool do_simp, bool turn_off_simp)  {
  budgetOff();
  assumptions.push(p);
  assumptions.push(q);
  assumptions.push(r);
  return solve_(do_simp, turn_off_simp);
 }
inline lbool SimpSolver::solve        (const vec<Lit>& assumps, bool do_simp, bool turn_off_simp){
  budgetOff(); assumps.copyTo(assumptions);
  return solve_(do_simp, turn_off_simp);
}

inline lbool SimpSolver::solveLimited (const vec<Lit>& assumps, bool do_simp, bool turn_off_simp){ 
    assumps.copyTo(assumptions); return solve_(do_simp, turn_off_simp); }

inline lbool SimpSolver::solveLimited (bool do_simp, bool turn_off_simp){ 
    return solve_(do_simp, turn_off_simp); }

//=================================================================================================
}  // namespace BVMinisat
}  // namespace cvc5

#endif

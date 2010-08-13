/************************************************************************************[SimpSolver.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

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

#ifndef SimpSolver_h
#define SimpSolver_h

#include <cstdio>

#include "Queue.h"
#include "Solver.h"


class SimpSolver : public Solver {
 public:
    // Constructor/Destructor:
    //
    SimpSolver();
    ~SimpSolver();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true);
    bool    addClause (vec<Lit>& ps);

    // Variable mode:
    // 
    void    setFrozen (Var v, bool b); // If a variable is frozen it will not be eliminated.

    // Solving:
    //
    bool    solve     (const vec<Lit>& assumps, bool do_simp = true, bool turn_off_simp = false);
    bool    solve     (bool do_simp = true, bool turn_off_simp = false);
    bool    eliminate (bool turn_off_elim = false);  // Perform variable elimination based simplification. 

    // Generate a (possibly simplified) DIMACS file:
    //
    void    toDimacs  (const char* file);

    // Mode of operation:
    //
    int     grow;             // Allow a variable elimination step to grow by a number of clauses (default to zero).
    bool    asymm_mode;       // Shrink clauses by asymmetric branching.
    bool    redundancy_check; // Check if a clause is already implied. Prett costly, and subsumes subsumptions :)

    // Statistics:
    //
    int     merges;
    int     asymm_lits;
    int     remembered_clauses;

// protected:
  public:

    // Helper structures:
    //
    struct ElimData {
        int          order;      // 0 means not eliminated, >0 gives an index in the elimination order
        vec<Clause*> eliminated;
        ElimData() : order(0) {} };

    struct ElimOrderLt {
        const vec<ElimData>& elimtable;
        ElimOrderLt(const vec<ElimData>& et) : elimtable(et) {}
        bool operator()(Var x, Var y) { return elimtable[x].order > elimtable[y].order; } };

    struct ElimLt {
        const vec<int>& n_occ;
        ElimLt(const vec<int>& no) : n_occ(no) {}
        int  cost      (Var x)        const { return n_occ[toInt(Lit(x))] * n_occ[toInt(~Lit(x))]; }
        bool operator()(Var x, Var y) const { return cost(x) < cost(y); } };


    // Solver state:
    //
    int                 elimorder;
    bool                use_simplification;
    vec<ElimData>       elimtable;
    vec<char>           touched;
    vec<vec<Clause*> >  occurs;
    vec<int>            n_occ;
    Heap<ElimLt>        elim_heap;
    Queue<Clause*>      subsumption_queue;
    vec<char>           frozen;
    int                 bwdsub_assigns;

    // Temporaries:
    //
    Clause*             bwdsub_tmpunit;

    // Main internal methods:
    //
    bool          asymm                    (Var v, Clause& c);
    bool          asymmVar                 (Var v);
    void          updateElimHeap           (Var v);
    void          cleanOcc                 (Var v);
    vec<Clause*>& getOccurs                (Var x);
    void          gatherTouchedClauses     ();
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause);
    bool          merge                    (const Clause& _ps, const Clause& _qs, Var v);
    bool          backwardSubsumptionCheck (bool verbose = false);
    bool          eliminateVar             (Var v, bool fail = false);
    void          remember                 (Var v);
    void          extendModel              ();
    void          verifyModel              ();

    void          removeClause             (Clause& c);
    bool          strengthenClause         (Clause& c, Lit l);
    void          cleanUpClauses           ();
    bool          implied                  (const vec<Lit>& c);
    void          toDimacs                 (FILE* f, Clause& c);
    bool          isEliminated             (Var v) const;

};


//=================================================================================================
// Implementation of inline methods:

inline void SimpSolver::updateElimHeap(Var v) {
    if (elimtable[v].order == 0)
        elim_heap.update(v); }

inline void SimpSolver::cleanOcc(Var v) {
    assert(use_simplification);
    Clause **begin = (Clause**)occurs[v];
    Clause **end = begin + occurs[v].size();
    Clause **i, **j;
    for (i = begin, j = end; i < j; i++)
        if ((*i)->mark() == 1){
            *i = *(--j);
            i--;
        }
    //occurs[v].shrink_(end - j);  // This seems slower. Why?!
    occurs[v].shrink(end - j);
}

inline vec<Clause*>& SimpSolver::getOccurs(Var x) {
    cleanOcc(x); return occurs[x]; }

inline bool  SimpSolver::isEliminated (Var v) const { return v < elimtable.size() && elimtable[v].order != 0; }
inline void  SimpSolver::setFrozen    (Var v, bool b) { frozen[v] = (char)b; if (b) { updateElimHeap(v); } }
inline bool  SimpSolver::solve        (bool do_simp, bool turn_off_simp) { vec<Lit> tmp; return solve(tmp, do_simp, turn_off_simp); }

//=================================================================================================
#endif

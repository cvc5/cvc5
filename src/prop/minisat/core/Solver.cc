/***************************************************************************************[Solver.cc]
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

#include <math.h>

#include <iostream>

#include "mtl/Sort.h"
#include "core/Solver.h"

#include "prop/sat.h"
#include "util/output.h"
#include "expr/command.h"

using namespace Minisat;
using namespace CVC4;
using namespace CVC4::prop;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 25, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 3, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));


class ScopedBool {
  bool& watch;
  bool oldValue;
public:
  ScopedBool(bool& watch, bool newValue)
  : watch(watch), oldValue(watch) {
    watch = newValue;
  }
  ~ScopedBool() {
    watch = oldValue;
  }
};


//=================================================================================================
// Constructor/Destructor:

Solver::Solver(CVC4::prop::SatSolver* proxy, CVC4::context::Context* context, bool enable_incremental) :
    proxy(proxy)
  , context(context)
  , assertionLevel(0)
  , enable_incremental(enable_incremental)
  , minisat_busy(false)
    // Parameters (user settable):
    //
  , verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor(1), learntsize_inc(1.5)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (!enable_incremental)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)
{}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar, bool theoryAtom)
{
    int v = nVars();

    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0, assertionLevel, -1));
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    theory   .push(theoryAtom);

    setDecisionVar(v, dvar);

    // If the variable is introduced at non-zero level, we need to reintroduce it on backtracks
    if (theoryAtom) {
      variables_to_register.push(VarIntroInfo(v, decisionLevel()));
    }

    Debug("minisat") << "new var " << v << std::endl;

    return v;
}


CRef Solver::reason(Var x) {

    // If we already have a reason, just return it
    if (vardata[x].reason != CRef_Lazy) return vardata[x].reason;

    // What's the literal we are trying to explain
    Lit l = mkLit(x, value(x) != l_True);

    // Get the explanation from the theory
    SatClause explanation;
    proxy->explainPropagation(l, explanation);

    // Sort the literals by trail index level
    lemma_lt lt(*this);
    sort(explanation, lt);
    Assert(explanation[0] == l);

    // Compute the assertion level for this clause
    int explLevel = 0;
    for (int i = 0; i < explanation.size(); ++ i) {
      int varLevel = intro_level(var(explanation[i]));
      if (varLevel > explLevel) {
        explLevel = varLevel;
      }
    }

    // Construct the reason (level 0)
    CRef real_reason = ca.alloc(explLevel, explanation, true);
    vardata[x] = mkVarData(real_reason, level(x), intro_level(x), trail_index(x));
    clauses_removable.push(real_reason);
    attachClause(real_reason);
    return real_reason;
}

bool Solver::addClause_(vec<Lit>& ps, bool removable)
{
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    // Check the clause for tautologies and similar
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
      if ((ps[i] == ~p) || (value(ps[i]) == l_True && level(var(ps[i])) == 0)) {
        // Clause can be ignored
        return true;
      }
      if ((ps[i] != p) && (value(ps[i]) != l_False || level(var(ps[i])) > 0)) {
        // This literal is a keeper
        ps[j++] = p = ps[i];
      }
    }

    // Fit to size
    ps.shrink(i - j);

    // If we are in solve or decision level > 0
    if (minisat_busy || decisionLevel() > 0) {
      lemmas.push();
      ps.copyTo(lemmas.last());
      lemmas_removable.push(removable);
    } else {
      // Add the clause and attach if not a lemma
      if (ps.size() == 0) {
          return ok = false;
      } else if (ps.size() == 1) {
        if(assigns[var(ps[0])] == l_Undef) {
          uncheckedEnqueue(ps[0]);
          if(assertionLevel > 0) {
            // remember to unset it on user pop
            Debug("minisat") << "got new unit " << ps[0] << " at assertion level " << assertionLevel << std::endl;
            trail_user.push(ps[0]);
          }
          return ok = (propagate(CHECK_WITHOUTH_PROPAGATION_QUICK) == CRef_Undef);
        } else return ok;
      } else {
        CRef cr = ca.alloc(assertionLevel, ps, false);
        clauses_persistent.push(cr);
	attachClause(cr);
      }
    }

    return true;
}


void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    Debug("minisat") << "Solver::attachClause(" << c << "): level " << c.level() << std::endl;
    Assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.removable()) learnts_literals += c.size();
    else            clauses_literals += c.size();
}


void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    Debug("minisat") << "Solver::detachClause(" << c << ")" << std::endl;
    assert(c.size() > 1);

    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.removable()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
    Debug("minisat") << "Solver::removeClause(" << c << ")" << std::endl;
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1);
    ca.free(cr);
}


bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    Debug("minisat") << "minisat::cancelUntil(" << level << ")" << std::endl;

    if (decisionLevel() > level){
        // Pop the SMT context
        for (int l = trail_lim.size() - level; l > 0; --l) {
          context->pop();
          if(Dump.isOn("state")) {
            Dump("state") << PopCommand() << std::endl;
          }
        }
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            if(intro_level(x) != -1) {// might be unregistered
              assigns [x] = l_Undef;
              vardata[x].trail_index = -1;
              if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
              insertVarOrder(x);
            }
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);

        // Register variables that have not been registered yet
        int currentLevel = decisionLevel();
        for(int i = variables_to_register.size() - 1; i >= 0 && variables_to_register[i].level > currentLevel; --i) {
          variables_to_register[i].level = currentLevel;
          proxy->variableNotify(variables_to_register[i].var);
        }
    }
}

void Solver::popTrail() {
  cancelUntil(0);
}

//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
#ifdef CVC4_REPLAY
    Lit nextLit = proxy->getNextReplayDecision();
    if (nextLit != lit_Undef) {
      return nextLit;
    }
#endif /* CVC4_REPLAY */

    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|      * returns the maximal level of the resolved clauses
|  
|________________________________________________________________________________________________@*/
int Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    int max_level = 0; // Maximal level of the resolved clauses

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.level() > max_level) {
          max_level = c.level();
        }

        if (c.removable())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++) {
            if (reason(var(out_learnt[i])) == CRef_Undef) {
                out_learnt[j++] = out_learnt[i];
            } else {
              // Check if the literal is redundant
              int red_level = litRedundant(out_learnt[i], abstract_level);
              if (red_level < 0) {
                // Literal is not redundant
                out_learnt[j++] = out_learnt[i];
              } else {
                // Literal is redundant, mark the level of the redundancy derivation
                if (max_level < red_level) {
                  max_level = red_level;
                }
              }
            }
        }
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

    // Return the maximal resolution level
    return max_level;
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
int Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    int max_level = 0;
    while (analyze_stack.size() > 0){
        CRef c_reason = reason(var(analyze_stack.last()));
        assert(c_reason != CRef_Undef);
        Clause& c = ca[c_reason];
        int c_size = c.size();
        analyze_stack.pop();
        if (c.level() > max_level) {
            max_level = c.level();
        }

        // Since calling reason might relocate to resize, c is not necesserily the right reference, we must
        // use the allocator each time
        for (int i = 1; i < c_size; i++){
            Lit p  = ca[c_reason][i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return -1;
                }
            }
        }
    }

    return max_level;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    Debug("minisat") << "unchecked enqueue of " << p << " (" << trail_index(var(p)) << ") trail size is " << trail.size() << " cap is " << trail.capacity() << std::endl;
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    if(trail_index(var(p)) != -1) {
      // This var is already represented in the trail, presumably from
      // an earlier incarnation as a unit clause (it has been
      // unregistered and renewed since then)
      vardata[var(p)] = mkVarData(from, decisionLevel(), intro_level(var(p)), trail_index(var(p)));
      trail[trail_index(var(p))] = p;
    } else {
      vardata[var(p)] = mkVarData(from, decisionLevel(), intro_level(var(p)), trail.size());
      trail.push_(p);
    }
    if (theory[var(p)]) {
      // Enqueue to the theory
      proxy->enqueueTheoryLiteral(p);
    }
}


CRef Solver::propagate(TheoryCheckType type)
{
    CRef confl = CRef_Undef;
    recheck = false;

    ScopedBool scoped_bool(minisat_busy, true);

    // If we are not in the quick mode add the lemmas that were left begind
    if (type != CHECK_WITHOUTH_PROPAGATION_QUICK && lemmas.size() > 0) {
      confl = updateLemmas();
      if (confl != CRef_Undef) {
        return confl;
      }
    }

    // If this is the final check, no need for Boolean propagation and
    // theory propagation
    if (type == CHECK_WITHOUTH_PROPAGATION_FINAL) {
      // Do the theory check
      theoryCheck(CVC4::theory::Theory::FULL_EFFORT);
      // If there are lemmas (or conflicts) update them
      if (lemmas.size() > 0) {
        recheck = true;
        return updateLemmas();
      } else {
        return confl;
      }
    }

    // The effort we will be using to theory check
    CVC4::theory::Theory::Effort effort = type == CHECK_WITHOUTH_PROPAGATION_QUICK ?
    		CVC4::theory::Theory::QUICK_CHECK : 
    		CVC4::theory::Theory::STANDARD;

    // Keep running until we have checked everything, we
    // have no conflict and no new literals have been asserted
    do {
        do {
          // Propagate on the clauses
          confl = propagateBool();

          // If no conflict, do the theory check
          if (confl == CRef_Undef) {
              // Do the theory check
              theoryCheck(effort);
              // If there are lemmas (or conflicts) update them
              if (lemmas.size() > 0) {
                  confl = updateLemmas();
              }
          }
        } while (confl == CRef_Undef && qhead < trail.size());

        // If still consistent do some theory propagation
        if (confl == CRef_Undef && type == CHECK_WITH_PROPAGATION_STANDARD) {
          propagateTheory();
          if (lemmas.size() > 0) {
              confl = updateLemmas();
          }
        }

    } while (confl == CRef_Undef && qhead < trail.size());

    return confl;
}

void Solver::propagateTheory() {
  std::vector<Lit> propagatedLiterals;
  proxy->theoryPropagate(propagatedLiterals);
  for (unsigned i = 0, i_end = propagatedLiterals.size(); i < i_end; ++ i) {
    Debug("minisat") << "Theory propagated: " << propagatedLiterals[i] << std::endl;
    uncheckedEnqueue(propagatedLiterals[i], CRef_Lazy);
  }
}

/*_________________________________________________________________________________________________
|
|  theoryCheck: [void]  ->  [Clause*]
|
|  Description:
|    Checks all enqueued theory facts for satisfiability. If a conflict arises, the conflicting
|    clause is returned, otherwise NULL.
|
|    Note: the propagation queue might be NOT empty
|________________________________________________________________________________________________@*/
void Solver::theoryCheck(CVC4::theory::Theory::Effort effort)
{
  proxy->theoryCheck(effort);
}

/*_________________________________________________________________________________________________
|
|  propagateBool : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagateBool()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            Assert(c.size() >= 2);
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
                uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / clauses_removable.size();    // Remove any clause below this activity

    sort(clauses_removable, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < clauses_removable.size(); i++){
        Clause& c = ca[clauses_removable[i]];
        if (c.size() > 2 && !locked(c) && (i < clauses_removable.size() / 2 || c.activity() < extra_lim))
            removeClause(clauses_removable[i]);
        else
            clauses_removable[j++] = clauses_removable[i];
    }
    clauses_removable.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void Solver::removeClausesAboveLevel(vec<CRef>& cs, int level)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.level() > level) {
            Debug("minisat") << "removeClausesAboveLevel(" << level << "): removing level-" << c.level() << " clause: " << c << std::endl;
            removeClause(cs[i]);
        } else {
            Debug("minisat") << "removeClausesAboveLevel(" << level << "): leaving level-" << c.level() << " clause: " << c << std::endl;
            cs[j++] = cs[i];
        }
    }
    Debug("minisat") << "removeClausesAboveLevel(" << level << "): removed " << i - j << " clauses in all, left " << j << std::endl;
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate(CHECK_WITHOUTH_PROPAGATION_QUICK) != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(clauses_removable);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses_persistent);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    TheoryCheckType check_type = CHECK_WITH_PROPAGATION_STANDARD;
    for (;;) {

        // Propagate and call the theory solvers
        CRef confl = propagate(check_type);
        Assert(lemmas.size() == 0);

        if (confl != CRef_Undef) {

          conflicts++; conflictC++;

          if (decisionLevel() == 0) return l_False;

            // Analyze the conflict
            learnt_clause.clear();
            int max_level = analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            // Assert the conflict clause and the asserting literal
            if (learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);
            } else {
                CRef cr = ca.alloc(max_level, learnt_clause, true);
                clauses_removable.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

             // We have a conflict so, we are going back to standard checks
            check_type = CHECK_WITH_PROPAGATION_STANDARD;
        } else {

	    // If this was a final check, we are satisfiable
            if (check_type == CHECK_WITHOUTH_PROPAGATION_FINAL) {
              // Unless a lemma has added more stuff to the queues
              if (!order_heap.empty() || qhead < trail.size()) {
                check_type = CHECK_WITH_PROPAGATION_STANDARD;
                continue;
              } else if (recheck) {
                // There some additional stuff added, so we go for another full-check
                continue;
              } else {
                // Yes, we're truly satisfiable
                return l_True;
              }
            }

            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()) {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                // [mdeters] notify theory engine of restarts for deferred
                // theory processing
                proxy->notifyRestart();
                return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                return l_False;
            }

            if (clauses_removable.size()-nAssigns() >= max_learnts) {
                // Reduce the set of learnt clauses:
                reduceDB();
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()) {
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True) {
                    // Dummy decision level:
                    newDecisionLevel();
                } else if (value(p) == l_False) {
                    analyzeFinal(~p, conflict);
                    return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef) {
                    // We need to do a full theory check to confirm
                    check_type = CHECK_WITHOUTH_PROPAGATION_FINAL;
                    continue;
                }

#ifdef CVC4_REPLAY
                proxy->logDecision(next);
#endif /* CVC4_REPLAY */
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
    Debug("minisat") << "nvars = " << nVars() << std::endl;

    ScopedBool scoped_bool(minisat_busy, true);

    popTrail();

    model.clear();
    conflict.clear();
    if (!ok){
      minisat_busy = false;
      return l_False;
    }

    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) {
          model[i] = value(i);
          Debug("minisat") << i << " = " << model[i] << std::endl;
        }
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses_persistent.size(); i++)
        if (!satisfied(ca[clauses_persistent[i]]))
            cnt++;
        
    for (int i = 0; i < clauses_persistent.size(); i++)
        if (!satisfied(ca[clauses_persistent[i]])){
            Clause& c = ca[clauses_persistent[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses_persistent.size(); i++)
        toDimacs(f, ca[clauses_persistent[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (hasReasonClause(v) && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < clauses_removable.size(); i++)
        ca.reloc(clauses_removable[i], to);

    // All original:
    //
    for (int i = 0; i < clauses_persistent.size(); i++)
        ca.reloc(clauses_persistent[i], to);
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void Solver::push()
{
  assert(enable_incremental);

  popTrail();
  ++assertionLevel;
  Debug("minisat") << "in user push, increasing assertion level to " << assertionLevel << std::endl;
  trail_user.push(lit_Undef);
  trail_ok.push(ok);
}

void Solver::pop()
{
  assert(enable_incremental);

  popTrail();

  --assertionLevel;

  Debug("minisat") << "in user pop, reducing assertion level to " << assertionLevel << " and removing clauses above this from db" << std::endl;

  // Remove all the clauses asserted (and implied) above the new base level
  removeClausesAboveLevel(clauses_removable, assertionLevel);
  removeClausesAboveLevel(clauses_persistent, assertionLevel);

  Debug("minisat") << "in user pop, at " << trail_lim.size() << " : " << assertionLevel << std::endl;

  // Unset any units learned or added at this level
  Debug("minisat") << "in user pop, unsetting level units for level " << assertionLevel << std::endl;
  while(trail_user.last() != lit_Undef) {
    Lit l = trail_user.last();
    Debug("minisat") << "== unassigning " << l << std::endl;
    Var      x  = var(l);
    assigns [x] = l_Undef;
    if (phase_saving >= 1)
      polarity[x] = sign(l);
    insertVarOrder(x);
    trail_user.pop();
  }
  trail_user.pop();
  ok = trail_ok.last();
  trail_ok.pop();
  Debug("minisat") << "in user pop, done unsetting level units" << std::endl;

  Debug("minisat") << "about to removeClausesAboveLevel(" << assertionLevel << ") in CNF" << std::endl;

  // Notify the cnf
  proxy->removeClausesAboveLevel(assertionLevel);
}

void Solver::unregisterVar(Lit lit) {
  Debug("minisat") << "unregisterVar " << lit << std::endl;
  Var v = var(lit);
  vardata[v].intro_level = -1;
  setDecisionVar(v, false);
}

void Solver::renewVar(Lit lit, int level) {
  Debug("minisat") << "renewVar " << lit << " " << level << std::endl;
  Var v = var(lit);
  vardata[v].intro_level = (level == -1 ? getAssertionLevel() : level);
  setDecisionVar(v, true);
}

CRef Solver::updateLemmas() {

  Debug("minisat::lemmas") << "Solver::updateLemmas()" << std::endl;

  CRef conflict = CRef_Undef;

  // Decision level to backtrack to
  int backtrackLevel = decisionLevel();

  // We use this comparison operator
  lemma_lt lt(*this);

  // Check for propagation and level to backtrack to
  for (int i = 0; i < lemmas.size(); ++ i)
  {
    // The current lemma
    vec<Lit>& lemma = lemmas[i];
    // If it's an empty lemma, we have a conflict at zero level
    if (lemma.size() == 0) {
      conflict = CRef_Lazy;
      backtrackLevel = 0;
      Debug("minisat::lemmas") << "Solver::updateLemmas(): found empty clause" << std::endl;
      continue;
    }
    // Sort the lemma to be able to attach
    sort(lemma, lt);
    // See if the lemma propagates something
    if (lemma.size() == 1 || value(lemma[1]) == l_False) {
      Debug("minisat::lemmas") << "found unit " << lemma.size() << std::endl;
      // This lemma propagates, see which level we need to backtrack to
      int currentBacktrackLevel = lemma.size() == 1 ? 0 : level(var(lemma[1]));
      // Even if the first literal is true, we should propagate it at this level (unless it's set at a lower level)
      if (value(lemma[0]) != l_True || level(var(lemma[0])) > currentBacktrackLevel) {
        if (currentBacktrackLevel < backtrackLevel) {
          backtrackLevel = currentBacktrackLevel;
        }
      }
    }
  }

  // Pop so that propagation would be current
  Debug("minisat::lemmas") << "Solver::updateLemmas(): backtracking to " << backtrackLevel << " from " << decisionLevel() << std::endl;
  cancelUntil(backtrackLevel);

  // Last index in the trail
  int backtrack_index = trail.size();

  // Attach all the clauses and enqueue all the propagations
  for (int i = 0; i < lemmas.size(); ++ i)
  {
    // The current lemma
    vec<Lit>& lemma = lemmas[i];
    bool removable = lemmas_removable[i];

    // Attach it if non-unit
    CRef lemma_ref = CRef_Undef;
    if (lemma.size() > 1) {
      lemma_ref = ca.alloc(assertionLevel, lemma, removable);
      if (removable) {
        clauses_removable.push(lemma_ref);
      } else {
        clauses_persistent.push(lemma_ref);
      }
      attachClause(lemma_ref);
    }

    // If the lemma is propagating enqueue its literal (or set the conflict)
    if (conflict == CRef_Undef && value(lemma[0]) != l_True) {
      if (lemma.size() == 1 || (value(lemma[1]) == l_False && trail_index(var(lemma[1])) < backtrack_index)) {
        if (value(lemma[0]) == l_False) {
          // We have a conflict
          if (lemma.size() > 1) {
            Debug("minisat::lemmas") << "Solver::updateLemmas(): conflict" << std::endl;
            conflict = lemma_ref;
          } else {
            Debug("minisat::lemmas") << "Solver::updateLemmas(): unit conflict or empty clause" << std::endl;
            conflict = CRef_Lazy;
          }
        } else {
//          if (Debug.isOn("minisat::lemmas")) {
//          	Debug("minisat::lemmas") << "Solver::updateLemmas(): " << lemma[0] << " from ";
//          	Clause& c = ca[lemma_ref];
//          	for (int i = 0; i < c.size(); ++ i) {
//          	   Debug("minisat::lemmas") << c[i] << "(" << value(c[i]) << "," << level(var(c[i])) << "," << trail_index(var(c[i])) << ") "; 
//          	} 
//			Debug("minisat::lemmas") << std::endl; 
//          }
          Debug("minisat::lemmas") << "lemma size is " << lemma.size() << std::endl;
          uncheckedEnqueue(lemma[0], lemma_ref);
          if(lemma.size() == 1 && assertionLevel > 0) {
            assert(decisionLevel() == 0);
            // remember to unset it on user pop
            Debug("minisat") << "got new unit (survived downward during updateLemmas()) " << lemma[0] << " at assertion level " << assertionLevel << std::endl;
            trail_user.push(lemma[0]);
          }
        }
      }
    }
  }

  // Clear the lemmas
  lemmas.clear();
  lemmas_removable.clear();

  return conflict;
}

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

#include "prop/bvminisat/core/Solver.h"

#include <math.h>

#include <vector>
#include <iostream>

#include "base/exception.h"
#include "base/output.h"
#include "options/bv_options.h"
#include "options/smt_options.h"
#include "proof/clause_id.h"
#include "proof/proof_manager.h"
#include "proof/resolution_bitvector_proof.h"
#include "proof/sat_proof.h"
#include "proof/sat_proof_implementation.h"
#include "prop/bvminisat/mtl/Sort.h"
#include "theory/interrupted.h"
#include "util/utility.h"

namespace CVC4 {
namespace BVMinisat {

#define OUTPUT_TAG "bvminisat: [a=" << assumptions.size() << ",l=" << decisionLevel() << "] "

std::ostream& operator << (std::ostream& out, const BVMinisat::Lit& l) {
  out << (sign(l) ? "-" : "") << var(l) + 1;
  return out;
}

std::ostream& operator << (std::ostream& out, const BVMinisat::Clause& c) {
  for (int i = 0; i < c.size(); i++) {
    if (i > 0) {
      out << " ";
    }
    out << c[i];
  }
  return out;
}


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

//=================================================================================================
// Proof declarations
CRef Solver::TCRef_Undef = CRef_Undef;
CRef Solver::TCRef_Lazy = CRef_Undef - 1; // no real lazy ref here


//=================================================================================================
// Constructor/Destructor:

Solver::Solver(CVC4::context::Context* context)
    :

      // Parameters (user settable):
      //
      d_notify(nullptr),
      c(context),
      verbosity(0),
      var_decay(opt_var_decay),
      clause_decay(opt_clause_decay),
      random_var_freq(opt_random_var_freq),
      random_seed(opt_random_seed),
      luby_restart(opt_luby_restart),
      ccmin_mode(opt_ccmin_mode),
      phase_saving(opt_phase_saving),
      rnd_pol(false),
      rnd_init_act(opt_rnd_init_act),
      garbage_frac(opt_garbage_frac),
      restart_first(opt_restart_first),
      restart_inc(opt_restart_inc)

      // Parameters (the rest):
      //
      ,
      learntsize_factor((double)1 / (double)3),
      learntsize_inc(1.5)

      // Parameters (experimental):
      //
      ,
      learntsize_adjust_start_confl(100),
      learntsize_adjust_inc(1.5)

      // Statistics: (formerly in 'SolverStats')
      //
      ,
      solves(0),
      starts(0),
      decisions(0),
      rnd_decisions(0),
      propagations(0),
      conflicts(0),
      dec_vars(0),
      clauses_literals(0),
      learnts_literals(0),
      max_literals(0),
      tot_literals(0)

      ,
      need_to_propagate(false),
      only_bcp(false),
      clause_added(false),
      ok(true),
      cla_inc(1),
      var_inc(1),
      watches(WatcherDeleted(ca)),
      qhead(0),
      simpDB_assigns(-1),
      simpDB_props(0),
      order_heap(VarOrderLt(activity)),
      progress_estimate(0),
      remove_satisfied(true)

      ,
      ca()

      // even though these are temporaries and technically should be set
      // before calling, lets initialize them. this will reduces chances of
      // non-determinism in portfolio (parallel) solver if variables are
      // being (incorrectly) used without initialization.
      ,
      seen(),
      analyze_stack(),
      analyze_toclear(),
      add_tmp(),
      max_learnts(0.0),
      learntsize_adjust_confl(0.0),
      learntsize_adjust_cnt(0)

      // Resource constraints:
      //
      ,
      conflict_budget(-1),
      propagation_budget(-1),
      asynch_interrupt(false),
      d_bvp(NULL)
{
  // Create the constant variables
  varTrue = newVar(true, false);
  varFalse = newVar(false, false);

  // Assert the constants
  uncheckedEnqueue(mkLit(varTrue, false));
  uncheckedEnqueue(mkLit(varFalse, true));
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    marker   .push(0);
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);

    return v;
}


bool Solver::addClause_(vec<Lit>& ps, ClauseId& id)
{
    if (decisionLevel() > 0) {
      cancelUntil(0);
    }
    
    if (!ok) {
      id = ClauseIdUndef;
      return false;
    }

    // Check if clause is satisfied and remove false/duplicate literals:
    // TODO proof for duplicate literals removal?
    sort(ps);
    Lit p; int i, j;
    int falseLiteralsCount = 0;
    
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
      // tautologies are ignored
      if (value(ps[i]) == l_True || ps[i] == ~p) {
        id = ClauseIdUndef;
        return true;
      }

      // Ignore repeated literals
      if (ps[i] == p) {
        continue;
      }

      if (value(ps[i]) == l_False) {
        if (!THEORY_PROOF_ON())
          continue;
        ++falseLiteralsCount;
      }
      ps[j++] = p = ps[i];
    }
    
    ps.shrink(i - j);

    clause_added = true;

    Assert(falseLiteralsCount == 0 || THEORY_PROOF_ON());

    if(falseLiteralsCount == 0) {
      if (ps.size() == 0) {
        Assert(!THEORY_PROOF_ON());
        return ok = false;
      }
      else if (ps.size() == 1){
        if(d_bvp){ id = d_bvp->getSatProof()->registerUnitClause(ps[0], INPUT);}
        uncheckedEnqueue(ps[0]);
        CRef confl_ref = propagate();
        ok = (confl_ref == CRef_Undef);
        if(d_bvp){ if (!ok) d_bvp->getSatProof()->finalizeProof(confl_ref); }
        return ok;
      } else {
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
        if(d_bvp){ id = d_bvp->getSatProof()->registerClause(cr, INPUT);}
      }
      return ok; 
    }
    
    if (falseLiteralsCount != 0 && THEORY_PROOF_ON()) {
      // we are in a conflicting state
      if (ps.size() == falseLiteralsCount && falseLiteralsCount == 1) {
        if(d_bvp){ id = d_bvp->getSatProof()->storeUnitConflict(ps[0], INPUT); }
        if(d_bvp){ d_bvp->getSatProof()->finalizeProof(CVC4::BVMinisat::CRef_Lazy); }
        return ok = false;
      }

      assign_lt lt(*this);
      sort(ps, lt);
      
      CRef cr = ca.alloc(ps, false);
      clauses.push(cr);
      attachClause(cr);
      
      if(d_bvp){id = d_bvp->getSatProof()->registerClause(cr, INPUT);}

      if(ps.size() == falseLiteralsCount) {
        if(d_bvp){ d_bvp->getSatProof()->finalizeProof(cr); }
        return ok = false;
      }
      
      // Check if it propagates
      if (ps.size() == falseLiteralsCount + 1) {
        Clause& cl = ca[cr];

        Assert(value(cl[0]) == l_Undef);
        uncheckedEnqueue(cl[0], cr);
        Assert(cl.size() > 1);
        CRef confl = propagate();
        ok = (confl == CRef_Undef);
        if(!ok) {
          if(d_bvp){
            if(ca[confl].size() == 1) {
              id = d_bvp->getSatProof()->storeUnitConflict(ca[confl][0], LEARNT);
              d_bvp->getSatProof()->finalizeProof(CVC4::BVMinisat::CRef_Lazy);
            } else {
              d_bvp->getSatProof()->finalizeProof(confl);
            }
          }
        }
      }
    }
    return ok;
}

void Solver::attachClause(CRef cr) {
  const Clause& clause = ca[cr];
  assert(clause.size() > 1);
  watches[~clause[0]].push(Watcher(cr, clause[1]));
  watches[~clause[1]].push(Watcher(cr, clause[0]));
  if (clause.learnt())
    learnts_literals += clause.size();
  else
    clauses_literals += clause.size();
}

void Solver::detachClause(CRef cr, bool strict) {
  const Clause& clause = ca[cr];
  if (d_bvp)
  {
    d_bvp->getSatProof()->markDeleted(cr); }

  assert(clause.size() > 1);

  if (strict)
  {
    remove(watches[~clause[0]], Watcher(cr, clause[1]));
    remove(watches[~clause[1]], Watcher(cr, clause[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~clause[0]);
        watches.smudge(~clause[1]);
    }

    if (clause.learnt())
      learnts_literals -= clause.size();
    else
      clauses_literals -= clause.size();
}

void Solver::removeClause(CRef cr) {
  Clause& clause = ca[cr];
  detachClause(cr);
  // Don't leave pointers to free'd memory!
  if (locked(clause)) vardata[var(clause[0])].reason = CRef_Undef;
  clause.mark(1);
  ca.free(cr);
}

bool Solver::satisfied(const Clause& clause) const
{
  for (int i = 0; i < clause.size(); i++)
    if (value(clause[i]) == l_True) return true;
  return false;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
      Debug("bvminisat::explain") << OUTPUT_TAG << " backtracking to " << level << std::endl;
      for (int clause = trail.size() - 1; clause >= trail_lim[level]; clause--)
      {
        Var x = var(trail[clause]);
        assigns[x] = l_Undef;
        if (marker[x] == 2) marker[x] = 1;
        if (phase_saving > 1
            || ((phase_saving == 1) && clause > trail_lim.last()))
        {
          polarity[x] = sign(trail[clause]);
        }
        insertVarOrder(x);
      }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
    }
}


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
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
|  
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, UIP uip)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    bool done = false;
    
    if(d_bvp){ d_bvp->getSatProof()->startResChain(confl); }

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& clause = ca[confl];

        if (clause.learnt()) claBumpActivity(clause);

        for (int j = (p == lit_Undef) ? 0 : 1; j < clause.size(); j++)
        {
          Lit q = clause[j];

          if (!seen[var(q)] && level(var(q)) > 0)
          {
            varBumpActivity(var(q));
            seen[var(q)] = 1;
            if (level(var(q)) >= decisionLevel())
              pathC++;
            else
              out_learnt.push(q);
          }

          if (level(var(q)) == 0)
          {
            if (d_bvp)
            {
              d_bvp->getSatProof()->resolveOutUnit(q);
            }
          }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

        if ( pathC > 0 && confl != CRef_Undef ) {
          if(d_bvp){ d_bvp->getSatProof()->addResolutionStep(p, confl, sign(p));}
        }

        switch (uip) {
        case UIP_FIRST:
          done = pathC == 0;
          break;
        case UIP_LAST:
          done = confl == CRef_Undef || (pathC == 0 && marker[var(p)] == 2);
          break;
        default:
          Unreachable();
          break;
        }
    } while (!done);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i1, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i1 = 1; i1 < out_learnt.size(); i1++)
          abstract_level |= abstractLevel(
              var(out_learnt[i1]));  // (maintain an abstraction of levels
                                     // involved in conflict)

        for (i1 = j = 1; i1 < out_learnt.size(); i1++)
        {
          if (reason(var(out_learnt[i1])) == CRef_Undef)
          {
            out_learnt[j++] = out_learnt[i1];
          }
          else
          {
            // Check if the literal is redundant
            if (!litRedundant(out_learnt[i1], abstract_level))
            {
              // Literal is not redundant
              out_learnt[j++] = out_learnt[i1];
            }
            else
            {
              if (d_bvp)
              {
                d_bvp->getSatProof()->storeLitRedundant(out_learnt[i1]);
              }
            }
          }
        }
    }else if (ccmin_mode == 1){
        Unreachable();
        for (i1 = j = 1; i1 < out_learnt.size(); i1++)
        {
          Var x = var(out_learnt[i1]);

          if (reason(x) == CRef_Undef)
            out_learnt[j++] = out_learnt[i1];
          else
          {
            Clause& clause = ca[reason(var(out_learnt[i1]))];
            for (int k = 1; k < clause.size(); k++)
              if (!seen[var(clause[k])] && level(var(clause[k])) > 0)
              {
                out_learnt[j++] = out_learnt[i1];
                break;
              }
          }
        }
    }else
      i1 = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i1 - j);
    tot_literals += out_learnt.size();

    for (int i2 = 0; i2 < out_learnt.size(); ++i2)
    {
      if (marker[var(out_learnt[i2])] == 0)
      {
        break;
      }
    }

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1) {
      out_btlevel = 0;
    }
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i3 = 2; i3 < out_learnt.size(); i3++)
          if (level(var(out_learnt[i3])) > level(var(out_learnt[max_i])))
            max_i = i3;
        // Swap-in this literal at i1 1:
        Lit p2 = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p2;
        out_btlevel = level(var(p2));
    }

    for (int j2 = 0; j2 < analyze_toclear.size(); j2++)
      seen[var(analyze_toclear[j2])] = 0;  // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        CRef c_reason = reason(var(analyze_stack.last()));
        assert(c_reason != CRef_Undef);
        Clause& clause = ca[c_reason];
        int c_size = clause.size();
        analyze_stack.pop();

        for (int i = 1; i < c_size; i++){
          Lit p2 = clause[i];
          if (!seen[var(p2)] && level(var(p2)) > 0)
          {
            if (reason(var(p2)) != CRef_Undef
                && (abstractLevel(var(p2)) & abstract_levels) != 0)
            {
              seen[var(p2)] = 1;
              analyze_stack.push(p2);
              analyze_toclear.push(p2);
            }
            else
            {
              for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
              analyze_toclear.shrink(analyze_toclear.size() - top);
              return false;
            }
          }
        }
    }

    return true;
}

/** 
 * Specialized analyzeFinal procedure where we test the consistency
 * of the assumptions before backtracking bellow the assumption level.
 * 
 * @param p the original uip (may be unit)
 * @param confl_clause the conflict clause
 * @param out_conflict the conflict in terms of assumptions we are building
 */
void Solver::analyzeFinal2(Lit p, CRef confl_clause, vec<Lit>& out_conflict) {
  assert (confl_clause != CRef_Undef);
  assert (decisionLevel() == assumptions.size());
  assert (level(var(p)) == assumptions.size());

  out_conflict.clear(); 
  
  Clause& cl = ca[confl_clause];
  for (int i = 0; i < cl.size(); ++i) {
    seen[var(cl[i])] = 1;
  }

  int end = options::proof() ? 0 :  trail_lim[0];
  for (int i = trail.size() - 1; i >= end; i--) {
    Var x = var(trail[i]);
    if (seen[x]) {
      if (reason(x) == CRef_Undef) {
        // we skip p if was a learnt unit
        if (x != var(p)) {
          if (marker[x] == 2) {
            assert (level(x) > 0);
            out_conflict.push(~trail[i]);
          } else {
            if(d_bvp){d_bvp->getSatProof()->resolveOutUnit(~(trail[i])); }
          }
        } else {
          if(d_bvp){d_bvp->getSatProof()->resolveOutUnit(~p);} 
        }
      } else {
        Clause& clause = ca[reason(x)];
        if(d_bvp){d_bvp->getSatProof()->addResolutionStep(trail[i],reason(x), sign(trail[i]));}

        for (int j = 1; j < clause.size(); j++)
        {
          if (level(var(clause[j])) > 0) seen[var(clause[j])] = 1;
          if(d_bvp){
            if (level(var(clause[j])) == 0)
            {
              d_bvp->getSatProof()->resolveOutUnit(clause[j]);
              seen[var(clause[j])] =
                  0;  // we don't need to resolve it out again
            }
          }
        }
      }
      seen[x] = 0;
    }
    assert (seen[x] == 0); 
  }
  assert (out_conflict.size()); 
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
    if (marker[var(p)] == 2) {
      out_conflict.push(p);
    }

    if(d_bvp){
      if (level(var(p)) == 0 && d_bvp->isAssumptionConflict()) {
        Assert(marker[var(p)] == 2);
        if (reason(var(p)) == CRef_Undef) {
          d_bvp->startBVConflict(p);
        }
      }
    }
    
    if (decisionLevel() == 0 && !options::proof()) {
      return;
    }

    seen[var(p)] = 1;
    int end = options::proof() ? 0 : trail_lim[0];
    
    for (int i = trail.size()-1; i >= end; i--){
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
              assert(marker[x] == 2);
              assert(level(x) > 0);
              if (~trail[i] != p)
              {
                out_conflict.push(~trail[i]);
              }
            } else {
              Clause& clause = ca[reason(x)];
              if(d_bvp){
                    if (d_bvp->isAssumptionConflict() &&
                        trail[i] == p) {
                      d_bvp->startBVConflict(reason(x));
                    } else {
                      d_bvp->getSatProof()->addResolutionStep(trail[i], reason(x), sign(trail[i]));
                    }
              }
              for (int j = 1; j < clause.size(); j++)
              {
                if (level(var(clause[j])) > 0)
                {
                  seen[var(clause[j])] = 1;
                }
                if(d_bvp){
                  if (level(var(clause[j])) == 0)
                  {
                    d_bvp->getSatProof()->resolveOutUnit(clause[j]);
                  }
                }
              }
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
    assert (out_conflict.size());
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
    if (decisionLevel() <= assumptions.size() && marker[var(p)] == 1) {
      if (d_notify) {
        Debug("bvminisat::explain")
            << OUTPUT_TAG << "propagating " << p << std::endl;
        d_notify->notify(p);
      }
    }
}

void Solver::popAssumption() {
    assumptions.pop();
    conflict.clear();
    cancelUntil(assumptions.size());
}

lbool Solver::propagateAssumptions() {
  only_bcp = true;
  ccmin_mode = 0;
  return search(-1);
}

lbool Solver::assertAssumption(Lit p, bool propagate) {
  // TODO need to somehow mark the assumption as unit in the current context?
  // it's not always unit though, but this would be useful for debugging
  
  // assert(marker[var(p)] == 1);

 
  if (decisionLevel() > assumptions.size()) {
    cancelUntil(assumptions.size());
  }

  conflict.clear();

  // add to the assumptions
  if (c->getLevel() > 0) {
    assumptions.push(p);
  } else {
    ClauseId id;
    if (!addClause(p, id)) {
      conflict.push(~p);
      return l_False;
    }
  }

  // run the propagation
  if (propagate) {
    only_bcp = true;
    ccmin_mode = 0; 
    lbool result = search(-1);
    return result; 
  } else {
    return l_True;
  }
}

void Solver::addMarkerLiteral(Var var) {
  // make sure it wasn't already marked
  Assert(marker[var] == 0);
  marker[var] = 1;
  if(d_bvp){d_bvp->getSatProof()->registerAssumption(var);}
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
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
            Clause& clause = ca[cr];
            Lit      false_lit = ~p;
            if (clause[0] == false_lit)
              clause[0] = clause[1], clause[1] = false_lit;
            assert(clause[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit first = clause[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < clause.size(); k++)
              if (value(clause[k]) != l_False)
              {
                clause[1] = clause[k];
                clause[k] = false_lit;
                watches[~clause[1]].push(w);
                goto NextClause;
              }

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
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
      Clause& clause = ca[learnts[i]];
      if (clause.size() > 2 && !locked(clause)
          && (i < learnts.size() / 2 || clause.activity() < extra_lim))
        removeClause(learnts[i]);
      else
        learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
      Clause& clause = ca[cs[i]];
      if (satisfied(clause))
      {
        if (locked(clause))
        {
          // store a resolution of the literal clause propagated
          if (d_bvp)
          {
            d_bvp->getSatProof()->storeUnitResolution(clause[0]);
          }
        }
        removeClause(cs[i]);
      }
        else
            cs[j++] = cs[i];
    }
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

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
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
lbool Solver::search(int nof_conflicts, UIP uip)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        CRef confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;

            if (decisionLevel() == 0) {
              // can this happen for bv?
              if(d_bvp){ d_bvp->getSatProof()->finalizeProof(confl);}
              return l_False;
            }

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, uip);

            Lit p = learnt_clause[0];
            //bool assumption = marker[var(p)] == 2;

            CRef cr = CRef_Undef;
            if (learnt_clause.size() > 1) {
              cr = ca.alloc(learnt_clause, true);
              learnts.push(cr);
              attachClause(cr);
              claBumpActivity(ca[cr]);
              if(d_bvp){
                 ClauseId id = d_bvp->getSatProof()->registerClause(cr, LEARNT);
                 PSTATS(
                 std::unordered_set<int> cl_levels;
                 for (int i = 0; i < learnt_clause.size(); ++i) {
                   cl_levels.insert(level(var(learnt_clause[i])));
                 }
                 if( d_bvp ){ d_bvp->getSatProof()->storeClauseGlue(id, cl_levels.size()); }
                       )
                 d_bvp->getSatProof()->endResChain(id);
              }
            }
            
            if (learnt_clause.size() == 1) {
              // learning a unit clause
              if(d_bvp){ d_bvp->getSatProof()->endResChain(learnt_clause[0]);}
            }
            
            //  if the uip was an assumption we are unsat
            if (level(var(p)) <= assumptions.size()) {
              for (int i = 0; i < learnt_clause.size(); ++i) {
                assert (level(var(learnt_clause[i])) <= decisionLevel()); 
                seen[var(learnt_clause[i])] = 1;
              }

              // Starting new resolution chain for bit-vector proof
              if( d_bvp ){
                if (cr == CRef_Undef) {
                  d_bvp->startBVConflict(learnt_clause[0]);
                }
                else { 
                  d_bvp->startBVConflict(cr);
                }
              }
              analyzeFinal(p, conflict);
              if(d_bvp){ d_bvp->endBVConflict(conflict); }
              Debug("bvminisat::search") << OUTPUT_TAG << " conflict on assumptions " << std::endl;
              return l_False;
            }

            if (!CVC4::options::bvEagerExplanations()) {
              // check if uip leads to a conflict 
              if (backtrack_level < assumptions.size()) {
                cancelUntil(assumptions.size());
                uncheckedEnqueue(p, cr);
              
                CRef new_confl = propagate();
                if (new_confl != CRef_Undef) {
                  // we have a conflict we now need to explain it
                  // TODO: proof for analyzeFinal2
                  if(d_bvp){ d_bvp->startBVConflict(new_confl); }
                  analyzeFinal2(p, new_confl, conflict);
                  if(d_bvp){ d_bvp->endBVConflict(conflict); }
                  return l_False;
                }
              }
            }

            cancelUntil(backtrack_level);
            uncheckedEnqueue(p, cr);
    
         
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

        }else{
            // NO CONFLICT
            bool isWithinBudget;
            try {
              isWithinBudget =
                  withinBudget(ResourceManager::Resource::BvSatConflictsStep);
            }
            catch (const CVC4::theory::Interrupted& e) {
              // do some clean-up and rethrow 
              cancelUntil(assumptions.size()); 
              throw e; 
            }

            if ((decisionLevel() > assumptions.size() && nof_conflicts >= 0
                 && conflictC >= nof_conflicts)
                || !isWithinBudget)
            {
              // Reached bound on number of conflicts:
              Debug("bvminisat::search")
                  << OUTPUT_TAG << " restarting " << std::endl;
              progress_estimate = progressEstimate();
              cancelUntil(assumptions.size());
              return l_Undef;
            }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify()) {
                Debug("bvminisat::search") << OUTPUT_TAG << " base level conflict, we're unsat" << std::endl;
                return l_False;
            }

            // We can't erase clauses if there is unprocessed assumptions, there might be some
            // propagationg we need to redu
            if (decisionLevel() >= assumptions.size() && learnts.size()-nAssigns() >= max_learnts) {
                // Reduce the set of learnt clauses:
                Debug("bvminisat::search") << OUTPUT_TAG << " cleaning up database" << std::endl;
                reduceDB();
            }

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    marker[var(p)] = 2;
                    
                    if(d_bvp){  d_bvp->markAssumptionConflict(); }
                    analyzeFinal(~p, conflict);
                    if(d_bvp){ d_bvp->endBVConflict(conflict); }
                    Debug("bvminisat::search") << OUTPUT_TAG << " assumption false, we're unsat" << std::endl;
                    return l_False;
                }else{
                    marker[var(p)] = 2;
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){

                if (only_bcp) {
                  Debug("bvminisat::search") << OUTPUT_TAG << " only bcp, skipping rest of the problem" << std::endl;
                  return l_True;
                }

                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef) {
                    Debug("bvminisat::search") << OUTPUT_TAG << " satisfiable" << std::endl;
                    // Model found:
                    return l_True;
                }
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
    Debug("bvminisat") <<"BVMinisat::Solving learned clauses " << learnts.size() <<"\n";
    Debug("bvminisat") <<"BVMinisat::Solving assumptions " << assumptions.size() <<"\n";

    model.clear();
    conflict.clear();

    ccmin_mode = 0;
    
    if (!ok) return l_False;

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
        if (!withinBudget(ResourceManager::Resource::BvSatConflictsStep)) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");

    if (status == l_True){
        // Extend & copy model:
        // model.growTo(nVars());
        // for (int i = 0; i < nVars(); i++) model[i] = value(i);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    return status;
}

//=================================================================================================
// Bitvector propagations
// 

void Solver::explain(Lit p, std::vector<Lit>& explanation) {
  Debug("bvminisat::explain") << OUTPUT_TAG << "starting explain of " << p << std::endl;

  // top level fact, no explanation necessary
  if (level(var(p)) == 0) {
    if(d_bvp){
          // the only way a marker variable is 
       if (reason(var(p)) == CRef_Undef) {
          d_bvp->startBVConflict(p);
          vec<Lit> confl;
          confl.push(p);
          d_bvp->endBVConflict(confl);
          return;
       }
    }
    if (!THEORY_PROOF_ON())
      return;
  }
  
  seen[var(p)] = 1;

  // if we are called at decisionLevel = 0 trail_lim is empty
  int bottom = options::proof() ? 0 : trail_lim[0];
  for (int i = trail.size()-1; i >= bottom; i--){
    Var x = var(trail[i]);
    if (seen[x]) {
      if (reason(x) == CRef_Undef) {
        if (marker[x] == 2) {
          assert(level(x) > 0);
          explanation.push_back(trail[i]);
        } else {
          Assert(level(x) == 0);
          if(d_bvp){ d_bvp->getSatProof()->resolveOutUnit(~(trail[i])); }
         }
        
      } else {
        Clause& clause = ca[reason(x)];
        if(d_bvp){
          if (p == trail[i]) {
            d_bvp->startBVConflict(reason(var(p)));
          } else {
            d_bvp->getSatProof()->addResolutionStep(trail[i], reason(x), sign(trail[i]));
          }
        }
        for (int j = 1; j < clause.size(); j++)
        {
          if (level(var(clause[j])) > 0 || options::proof())
          {
            seen[var(clause[j])] = 1;
          }
        }
      }
      seen[x] = 0;
    }
  }
  seen[var(p)] = 0;

  if(d_bvp){
    vec<Lit> conflict_clause;
    conflict_clause.push(p);
    for(unsigned i = 0; i < explanation.size(); ++i) {
      conflict_clause.push(~explanation[i]);
    }
    d_bvp->endBVConflict(conflict_clause);
  }
}

void Solver::setProofLog(proof::ResolutionBitVectorProof* bvp)
{
  d_bvp = bvp;
  d_bvp->initSatProof(this);
  d_bvp->getSatProof()->registerTrueLit(mkLit(varTrue, false));
  d_bvp->getSatProof()->registerFalseLit(mkLit(varFalse, true));
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

void Solver::toDimacs(FILE* f, Clause& clause, vec<Var>& map, Var& max)
{
  if (satisfied(clause)) return;

  for (int i = 0; i < clause.size(); i++)
    if (value(clause[i]) != l_False)
      fprintf(f,
              "%s%d ",
              sign(clause[i]) ? "-" : "",
              mapVar(var(clause[i]), map, max) + 1);
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
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
          Clause& clause = ca[clauses[i]];
          for (int j = 0; j < clause.size(); j++)
            if (value(clause[j]) != l_False) mapVar(var(clause[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumps.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumps.size(); i++){
        assert(value(assumps[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumps[i]) ? "-" : "", mapVar(var(assumps[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

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
              ca.reloc(ws[j].cref, to, d_bvp ? d_bvp->getSatProof() : NULL);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
          ca.reloc(vardata[v].reason, to, d_bvp ? d_bvp->getSatProof() : NULL);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
      ca.reloc(learnts[i], to, d_bvp ? d_bvp->getSatProof() : NULL);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
      ca.reloc(clauses[i], to, d_bvp ? d_bvp->getSatProof() : NULL);

    if(d_bvp){ d_bvp->getSatProof()->finishUpdateCRef(); }
}


void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 
    Debug("bvminisat") << " BVMinisat::Garbage collection \n"; 
    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void ClauseAllocator::reloc(CRef& cr,
                            ClauseAllocator& to,
                            CVC4::TSatProof<Solver>* proof)
{
  CRef old = cr;  // save the old reference

  Clause& c = operator[](cr);
  if (c.reloced()) { cr = c.relocation(); return; }
  
  cr = to.alloc(c, c.learnt());
  c.relocate(cr);
  if (proof)
  {
    proof->updateCRef(old, cr);
  }
  
  // Copy extra data-fields: 
  // (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
  to[cr].mark(c.mark());
  if (to[cr].learnt())         to[cr].activity() = c.activity();
  else if (to[cr].has_extra()) to[cr].calcAbstraction();
}

void Solver::setNotify(Notify* toNotify) { d_notify = toNotify; }
bool Solver::withinBudget(ResourceManager::Resource r) const
{
  AlwaysAssert(d_notify);
  d_notify->safePoint(r);

  return !asynch_interrupt &&
         (conflict_budget < 0 || conflicts < (uint64_t)conflict_budget) &&
         (propagation_budget < 0 ||
          propagations < (uint64_t)propagation_budget);
}

} /* CVC4::BVMinisat namespace */
} /* CVC4 namespace */

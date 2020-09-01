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

#include "prop/minisat/core/Solver.h"

#include <math.h>

#include <iostream>
#include <unordered_set>

#include "base/output.h"
#include "options/main_options.h"
#include "options/prop_options.h"
#include "options/smt_options.h"
#include "proof/clause_id.h"
#include "proof/cnf_proof.h"
#include "proof/proof_manager.h"
#include "proof/sat_proof.h"
#include "proof/sat_proof_implementation.h"
#include "prop/minisat/minisat.h"
#include "prop/minisat/mtl/Sort.h"
#include "prop/theory_proxy.h"

using namespace CVC4::prop;

namespace CVC4 {
namespace Minisat {

namespace {
/*
 * Returns true if the solver should add all clauses at the current assertion
 * level.
 *
 * FIXME: This is a workaround. Currently, our resolution proofs do not
 * handle clauses with a lower-than-assertion-level correctly because the
 * resolution proofs get removed when popping the context but the SAT solver
 * keeps using them.
 */
bool assertionLevelOnly()
{
  return options::unsatCores() && options::incrementalSolving();
}

//=================================================================================================
// Helper functions for decision tree tracing

// Writes to Trace macro for decision tree tracing
static inline void dtviewDecisionHelper(size_t level,
                                        const Node& node,
                                        const char* decisiontype)
{
  Trace("dtview") << std::string(level - (options::incrementalSolving() ? 1 : 0), '*')
                  << " " << node << " :" << decisiontype << "-DECISION:" << std::endl;
}

// Writes to Trace macro for propagation tracing
static inline void dtviewPropagationHeaderHelper(size_t level)
{
  Trace("dtview::prop") << std::string(level + 1 - (options::incrementalSolving() ? 1 : 0),
                                       '*')
                        << " /Propagations/" << std::endl;
}

// Writes to Trace macro for propagation tracing
static inline void dtviewBoolPropagationHelper(size_t level,
                                               Lit& l,
                                               CVC4::prop::TheoryProxy* proxy)
{
  Trace("dtview::prop") << std::string(
      level + 1 - (options::incrementalSolving() ? 1 : 0), ' ')
                        << ":BOOL-PROP: "
                        << proxy->getNode(MinisatSatSolver::toSatLiteral(l))
                        << std::endl;
}

// Writes to Trace macro for conflict tracing
static inline void dtviewPropConflictHelper(size_t level,
                                            Clause& confl,
                                            CVC4::prop::TheoryProxy* proxy)
{
  Trace("dtview::conflict")
      << std::string(level + 1 - (options::incrementalSolving() ? 1 : 0), ' ')
      << ":PROP-CONFLICT: (or";
  for (int i = 0; i < confl.size(); i++)
  {
    Trace("dtview::conflict")
        << " " << proxy->getNode(MinisatSatSolver::toSatLiteral(confl[i]));
  }
  Trace("dtview::conflict") << ")" << std::endl;
}

}  // namespace

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
CRef Solver::TCRef_Lazy = CRef_Lazy;

class ScopedBool
{
  bool& d_watch;
  bool d_oldValue;

 public:
  ScopedBool(bool& watch, bool newValue) : d_watch(watch), d_oldValue(watch)
  {
    watch = newValue;
  }
  ~ScopedBool() { d_watch = d_oldValue; }
};

//=================================================================================================
// Constructor/Destructor:

Solver::Solver(CVC4::prop::TheoryProxy* proxy,
               CVC4::context::Context* context,
               bool enable_incremental)
    : d_proxy(proxy),
      d_context(context),
      assertionLevel(0),
      d_enable_incremental(enable_incremental),
      minisat_busy(false)
      // Parameters (user settable):
      //
      ,
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
      learntsize_factor(1),
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
      resources_consumed(0),
      dec_vars(0),
      clauses_literals(0),
      learnts_literals(0),
      max_literals(0),
      tot_literals(0)

      ,
      ok(true),
      cla_inc(1),
      var_inc(1),
      watches(WatcherDeleted(ca)),
      qhead(0),
      simpDB_assigns(-1),
      simpDB_props(0),
      order_heap(VarOrderLt(activity)),
      progress_estimate(0),
      remove_satisfied(!enable_incremental)

      // Resource constraints:
      //
      ,
      conflict_budget(-1),
      propagation_budget(-1),
      asynch_interrupt(false)
{
  if (options::unsatCores())
  {
    ProofManager::currentPM()->initSatProof(this);
  }

  // Create the constant variables
  varTrue = newVar(true, false, false);
  varFalse = newVar(false, false, false);

  // Assert the constants
  uncheckedEnqueue(mkLit(varTrue, false));
  uncheckedEnqueue(mkLit(varFalse, true));
  // FIXME: these should be axioms I believe
  if (options::unsatCores())
  {
    ProofManager::getSatProof()->registerTrueLit(mkLit(varTrue, false));
    ProofManager::getSatProof()->registerFalseLit(mkLit(varFalse, true));
  }
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar, bool isTheoryAtom, bool preRegister, bool canErase)
{
    int v = nVars();

    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(VarData(CRef_Undef, -1, -1, assertionLevel, -1));
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    theory   .push(isTheoryAtom);

    setDecisionVar(v, dvar);

    // If the variable is introduced at non-zero level, we need to reintroduce it on backtracks
    if (preRegister) {
      variables_to_register.push(VarIntroInfo(v, decisionLevel()));
    }

    Debug("minisat") << "new var " << v << std::endl;

    return v;
}

void Solver::resizeVars(int newSize) {
  assert(d_enable_incremental);
  assert(decisionLevel() == 0);
  Assert(newSize >= 2) << "always keep true/false";
  if (newSize < nVars()) {
    int shrinkSize = nVars() - newSize;

    // Resize watches up to the negated last literal
    watches.resizeTo(mkLit(newSize-1, true));

    // Resize all info arrays
    assigns.shrink(shrinkSize);
    vardata.shrink(shrinkSize);
    activity.shrink(shrinkSize);
    seen.shrink(shrinkSize);
    polarity.shrink(shrinkSize);
    decision.shrink(shrinkSize);
    theory.shrink(shrinkSize);

  }

  if (Debug.isOn("minisat::pop")) {
    for (int i = 0; i < trail.size(); ++ i) {
      assert(var(trail[i]) < nVars());
    }
  }
}

CRef Solver::reason(Var x) {
  Debug("pf::sat") << "Solver::reason(" << x << ")" << std::endl;

  // If we already have a reason, just return it
  if (vardata[x].d_reason != CRef_Lazy) return vardata[x].d_reason;

  // What's the literal we are trying to explain
  Lit l = mkLit(x, value(x) != l_True);

  // Get the explanation from the theory
  SatClause explanation_cl;
  // FIXME: at some point return a tag with the theory that spawned you
  d_proxy->explainPropagation(MinisatSatSolver::toSatLiteral(l),
                              explanation_cl);
  vec<Lit> explanation;
  MinisatSatSolver::toMinisatClause(explanation_cl, explanation);

  Debug("pf::sat") << "Solver::reason: explanation_cl = " << explanation_cl
                   << std::endl;

  // Sort the literals by trail index level
  lemma_lt lt(*this);
  sort(explanation, lt);
  Assert(explanation[0] == l);

  // Compute the assertion level for this clause
  int explLevel = 0;
  if (assertionLevelOnly())
  {
    explLevel = assertionLevel;
    }
    else
    {
      int i, j;
      Lit prev = lit_Undef;
      for (i = 0, j = 0; i < explanation.size(); ++i)
      {
        // This clause is valid theory propagation, so its level is the level of
        // the top literal
        explLevel = std::max(explLevel, intro_level(var(explanation[i])));

        Assert(value(explanation[i]) != l_Undef);
        Assert(i == 0
               || trail_index(var(explanation[0]))
                      > trail_index(var(explanation[i])));

        // Always keep the first literal
        if (i == 0)
        {
          prev = explanation[j++] = explanation[i];
          continue;
        }
        // Ignore duplicate literals
        if (explanation[i] == prev)
        {
          continue;
        }
        // Ignore zero level literals
        if (level(var(explanation[i])) == 0
            && user_level(var(explanation[i]) == 0))
        {
          continue;
        }
        // Keep this literal
        prev = explanation[j++] = explanation[i];
      }
      explanation.shrink(i - j);

      Debug("pf::sat") << "Solver::reason: explanation = ";
      for (int k = 0; k < explanation.size(); ++k)
      {
        Debug("pf::sat") << explanation[k] << " ";
      }
      Debug("pf::sat") << std::endl;

      // We need an explanation clause so we add a fake literal
      if (j == 1)
      {
        // Add not TRUE to the clause
        explanation.push(mkLit(varTrue, true));
      }
    }

    // Construct the reason
    CRef real_reason = ca.alloc(explLevel, explanation, true);
    // FIXME: at some point will need more information about where this explanation
    // came from (ie. the theory/sharing)
    Debug("pf::sat") << "Minisat::Solver registering a THEORY_LEMMA (1)" << std::endl;
    if (options::unsatCores())
    {
      ClauseId id = ProofManager::getSatProof()->registerClause(real_reason,
                                                                THEORY_LEMMA);
      // map id to assertion, which may be required if looking for
      // lemmas in unsat core
      ProofManager::getCnfProof()->registerConvertedClause(id);
      // explainPropagation() pushes the explanation on the assertion stack
      // in CnfProof, so we need to pop it here. This is important because
      // reason() may be called indirectly while adding a clause, which can
      // lead to a wrong assertion being associated with the clause being
      // added (see issue #2137).
      ProofManager::getCnfProof()->popCurrentAssertion();
    }
    vardata[x] = VarData(real_reason, level(x), user_level(x), intro_level(x), trail_index(x));
    clauses_removable.push(real_reason);
    attachClause(real_reason);

    return real_reason;
}

bool Solver::addClause_(vec<Lit>& ps, bool removable, ClauseId& id)
{
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;

    // Which user-level to assert this clause at
    int clauseLevel = (removable && !assertionLevelOnly()) ? 0 : assertionLevel;

    // Check the clause for tautologies and similar
    int falseLiteralsCount = 0;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++) {
      // Update the level
      clauseLevel = assertionLevelOnly()
                        ? assertionLevel
                        : std::max(clauseLevel, intro_level(var(ps[i])));
      // Tautologies are ignored
      if (ps[i] == ~p) {
        id = ClauseIdUndef;
        // Clause can be ignored
        return true;
      }
      // Clauses with 0-level true literals are also ignored
      if (value(ps[i]) == l_True && level(var(ps[i])) == 0 && user_level(var(ps[i])) == 0) {
        id = ClauseIdUndef;
        return true;
      }
      // Ignore repeated literals
      if (ps[i] == p) {
        continue;
      }
      // If a literal is false at 0 level (both sat and user level) we also ignore it
      if (value(ps[i]) == l_False) {
        if (!options::unsatCores() && level(var(ps[i])) == 0
            && user_level(var(ps[i])) == 0)
        {
          continue;
        }
        else
        {
          // If we decide to keep it, we count it into the false literals
          falseLiteralsCount ++;
        }
      }
      // This literal is a keeper
      ps[j++] = p = ps[i];
    }

    // Fit to size
    ps.shrink(i - j);

    // If we are in solve_ or propagate
    if (minisat_busy)
    {
      Debug("pf::sat") << "Add clause adding a new lemma: ";
      for (int k = 0; k < ps.size(); ++k) {
        Debug("pf::sat") << ps[k] << " ";
      }
      Debug("pf::sat") << std::endl;

      lemmas.push();
      ps.copyTo(lemmas.last());
      lemmas_removable.push(removable);
      if (options::unsatCores())
      {
        // Store the expression being converted to CNF until
        // the clause is actually created
        lemmas_cnf_assertion.push_back(
            ProofManager::getCnfProof()->getCurrentAssertion());
        id = ClauseIdUndef;
      }
    } else {
      assert(decisionLevel() == 0);

      // If all false, we're in conflict
      if (ps.size() == falseLiteralsCount) {
        if (options::unsatCores())
        {
          // Take care of false units here; otherwise, we need to
          // construct the clause below to give to the proof manager
          // as the final conflict.
          if(falseLiteralsCount == 1) {
            if (options::unsatCores())
            {
              ClauseKind ck =
                  ProofManager::getCnfProof()->getCurrentAssertionKind()
                      ? INPUT
                      : THEORY_LEMMA;
              id = ProofManager::getSatProof()->storeUnitConflict(ps[0], ck);
              // map id to assertion, which may be required if looking for
              // lemmas in unsat core
              if (ck == THEORY_LEMMA)
              {
                ProofManager::getCnfProof()->registerConvertedClause(id);
              }
              ProofManager::getSatProof()->finalizeProof(
                  CVC4::Minisat::CRef_Lazy);
            }
            return ok = false;
          }
        }
        else
        {
          return ok = false;
        }
      }

      CRef cr = CRef_Undef;

      // If not unit, add the clause
      if (ps.size() > 1) {

        lemma_lt lt(*this);
        sort(ps, lt);

        cr = ca.alloc(clauseLevel, ps, false);
        clauses_persistent.push(cr);
        attachClause(cr);

        if (options::unsatCores())
        {
          ClauseKind ck = ProofManager::getCnfProof()->getCurrentAssertionKind()
                              ? INPUT
                              : THEORY_LEMMA;
          id = ProofManager::getSatProof()->registerClause(cr, ck);
          // map id to assertion, which may be required if looking for
          // lemmas in unsat core
          if (ck == THEORY_LEMMA)
          {
            ProofManager::getCnfProof()->registerConvertedClause(id);
          }
          if (ps.size() == falseLiteralsCount)
          {
            ProofManager::getSatProof()->finalizeProof(cr);
            return ok = false;
          }
        }
      }

      // Check if it propagates
      if (ps.size() == falseLiteralsCount + 1) {
        if(assigns[var(ps[0])] == l_Undef) {
          assert(assigns[var(ps[0])] != l_False);
          uncheckedEnqueue(ps[0], cr);
          Debug("cores") << "i'm registering a unit clause, maybe input"
                         << std::endl;
          if (options::unsatCores() && ps.size() == 1)
          {
            ClauseKind ck =
                ProofManager::getCnfProof()->getCurrentAssertionKind()
                    ? INPUT
                    : THEORY_LEMMA;
            id = ProofManager::getSatProof()->registerUnitClause(ps[0], ck);
            // map id to assertion, which may be required if looking for
            // lemmas in unsat core
            if (ck == THEORY_LEMMA)
            {
              ProofManager::getCnfProof()->registerConvertedClause(id);
            }
          }
          CRef confl = propagate(CHECK_WITHOUT_THEORY);
          if(! (ok = (confl == CRef_Undef)) ) {
            if (options::unsatCores())
            {
              if (ca[confl].size() == 1)
              {
                id = ProofManager::getSatProof()->storeUnitConflict(
                    ca[confl][0], LEARNT);
                ProofManager::getSatProof()->finalizeProof(
                    CVC4::Minisat::CRef_Lazy);
              }
              else
              {
                ProofManager::getSatProof()->finalizeProof(confl);
              }
            }
          }
          return ok;
        } else {
          if (options::unsatCores())
          {
            id = ClauseIdUndef;
          }
          return ok;
        }
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
    if (options::unsatCores())
    {
      ProofManager::getSatProof()->markDeleted(cr);
    }
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
    Debug("minisat::remove-clause") << "Solver::removeClause(" << c << ")" << std::endl;
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].d_reason = CRef_Undef;
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
          d_context->pop();
          if(Dump.isOn("state")) {
            d_proxy->dumpStatePop();
          }
        }
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            vardata[x].d_trail_index = -1;
            if ((phase_saving > 1 ||
                 ((phase_saving == 1) && c > trail_lim.last())
                 ) && ((polarity[x] & 0x2) == 0)) {
              polarity[x] = sign(trail[c]);
            }
            insertVarOrder(x);
        }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);
        flipped.shrink(flipped.size() - level);

        // Register variables that have not been registered yet
        int currentLevel = decisionLevel();
        for (int i = variables_to_register.size() - 1;
             i >= 0 && variables_to_register[i].d_level > currentLevel;
             --i)
        {
          variables_to_register[i].d_level = currentLevel;
          d_proxy->variableNotify(
              MinisatSatSolver::toSatVariable(variables_to_register[i].d_var));
        }
    }
}

void Solver::resetTrail() { cancelUntil(0); }

//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Lit nextLit;

    // Theory requests
    nextLit =
        MinisatSatSolver::toMinisatLit(d_proxy->getNextTheoryDecisionRequest());
    while (nextLit != lit_Undef) {
      if(value(var(nextLit)) == l_Undef) {
        Debug("theoryDecision")
            << "getNextTheoryDecisionRequest(): now deciding on " << nextLit
            << std::endl;
        decisions++;

        // org-mode tracing -- theory decision
        if (Trace.isOn("dtview"))
        {
          dtviewDecisionHelper(
              d_context->getLevel(),
              d_proxy->getNode(MinisatSatSolver::toSatLiteral(nextLit)),
              "THEORY");
        }

        if (Trace.isOn("dtview::prop"))
        {
          dtviewPropagationHeaderHelper(d_context->getLevel());
        }

        return nextLit;
      } else {
        Debug("theoryDecision")
            << "getNextTheoryDecisionRequest(): would decide on " << nextLit
            << " but it already has an assignment" << std::endl;
      }
      nextLit = MinisatSatSolver::toMinisatLit(
          d_proxy->getNextTheoryDecisionRequest());
    }
    Debug("theoryDecision")
        << "getNextTheoryDecisionRequest(): decide on another literal"
        << std::endl;

    // DE requests
    bool stopSearch = false;
    nextLit = MinisatSatSolver::toMinisatLit(
        d_proxy->getNextDecisionEngineRequest(stopSearch));
    if(stopSearch) {
      return lit_Undef;
    }
    if(nextLit != lit_Undef) {
      Assert(value(var(nextLit)) == l_Undef)
          << "literal to decide already has value";
      decisions++;
      Var next = var(nextLit);
      if(polarity[next] & 0x2) {
        nextLit = mkLit(next, polarity[next] & 0x1);
      }

      // org-mode tracing -- decision engine decision
      if (Trace.isOn("dtview"))
      {
        dtviewDecisionHelper(
            d_context->getLevel(),
            d_proxy->getNode(MinisatSatSolver::toSatLiteral(nextLit)),
            "DE");
      }

      if (Trace.isOn("dtview::prop"))
      {
        dtviewPropagationHeaderHelper(d_context->getLevel());
      }

      return nextLit;
    }

    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next >= nVars() || next == var_Undef || value(next) != l_Undef || !decision[next]) {
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else {
            next = order_heap.removeMin();
        }

        if(!decision[next]) continue;
        // Check with decision engine about relevancy
        if (d_proxy->isDecisionRelevant(MinisatSatSolver::toSatVariable(next))
            == false)
        {
          next = var_Undef;
        }
    }

    if(next == var_Undef) {
      return lit_Undef;
    } else {
      decisions++;
      // Check with decision engine if it can tell polarity
      lbool dec_pol = MinisatSatSolver::toMinisatlbool(
          d_proxy->getDecisionPolarity(MinisatSatSolver::toSatVariable(next)));
      Lit decisionLit;
      if(dec_pol != l_Undef) {
        Assert(dec_pol == l_True || dec_pol == l_False);
        decisionLit = mkLit(next, (dec_pol == l_True));
      }
      else
      {
        // If it can't use internal heuristic to do that
        decisionLit = mkLit(
            next, rnd_pol ? drand(random_seed) < 0.5 : (polarity[next] & 0x1));
      }

      // org-mode tracing -- decision engine decision
      if (Trace.isOn("dtview"))
      {
        dtviewDecisionHelper(
            d_context->getLevel(),
            d_proxy->getNode(MinisatSatSolver::toSatLiteral(decisionLit)),
            "DE");
      }

      if (Trace.isOn("dtview::prop"))
      {
        dtviewPropagationHeaderHelper(d_context->getLevel());
      }

      return decisionLit;
    }
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

    int max_resolution_level = 0; // Maximal level of the resolved clauses

    if (options::unsatCores())
    {
      ProofManager::getSatProof()->startResChain(confl);
    }
    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)

        {
          // ! IMPORTANT !
          // It is not safe to use c after this block of code because
          // resolveOutUnit() below may lead to clauses being allocated, which
          // in turn may lead to reallocations that invalidate c.
          Clause& c = ca[confl];
          max_resolution_level = std::max(max_resolution_level, c.level());

          if (c.removable()) claBumpActivity(c);
        }

        for (int j = (p == lit_Undef) ? 0 : 1, size = ca[confl].size();
             j < size;
             j++)
        {
          Lit q = ca[confl][j];

          if (!seen[var(q)] && level(var(q)) > 0)
          {
            varBumpActivity(var(q));
            seen[var(q)] = 1;
            if (level(var(q)) >= decisionLevel())
              pathC++;
            else
              out_learnt.push(q);
          }
          else
          {
            // We could be resolving a literal propagated by a clause/theory
            // using information from a higher level
            if (!seen[var(q)] && level(var(q)) == 0)
            {
              max_resolution_level =
                  std::max(max_resolution_level, user_level(var(q)));
            }

            // FIXME: can we do it lazily if we actually need the proof?
            if (options::unsatCores() && level(var(q)) == 0)
            {
              ProofManager::getSatProof()->resolveOutUnit(q);
            }
          }
        }

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

        if (options::unsatCores() && pathC > 0 && confl != CRef_Undef)
        {
          ProofManager::getSatProof()->addResolutionStep(p, confl, sign(p));
        }

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
              if (!litRedundant(out_learnt[i], abstract_level)) {
                // Literal is not redundant
                out_learnt[j++] = out_learnt[i];
              } else {
                if (options::unsatCores())
                {
                  ProofManager::getSatProof()->storeLitRedundant(out_learnt[i]);
                }
                // Literal is redundant, to be safe, mark the level as current assertion level
                // TODO: maybe optimize
                max_resolution_level = std::max(max_resolution_level, user_level(var(out_learnt[i])));
              }
            }
        }

    }else if (ccmin_mode == 1){
        Unreachable();
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
        for (int k = 2; k < out_learnt.size(); k++)
          if (level(var(out_learnt[k])) > level(var(out_learnt[max_i])))
            max_i = k;
        // Swap-in this literal at index 1:
        Lit p2 = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1] = p2;
        out_btlevel = level(var(p2));
    }

    for (int k = 0; k < analyze_toclear.size(); k++)
      seen[var(analyze_toclear[k])] = 0;  // ('seen[]' is now cleared)

    // Return the maximal resolution level
    return max_resolution_level;
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
        Clause& c = ca[c_reason];
        int c_size = c.size();
        analyze_stack.pop();

        // Since calling reason might relocate to resize, c is not necesserily the right reference, we must
        // use the allocator each time
        for (int i = 1; i < c_size; i++){
          Lit p2 = ca[c_reason][i];
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
    assert(var(p) < nVars());
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = VarData(from, decisionLevel(), assertionLevel, intro_level(var(p)), trail.size());
    trail.push_(p);
    if (theory[var(p)]) {
      // Enqueue to the theory
      d_proxy->enqueueTheoryLiteral(MinisatSatSolver::toSatLiteral(p));
    }
}


CRef Solver::propagate(TheoryCheckType type)
{
    CRef confl = CRef_Undef;
    recheck = false;
    theoryConflict = false;

    ScopedBool scoped_bool(minisat_busy, true);

    // Add lemmas that we're left behind
    if (lemmas.size() > 0) {
      confl = updateLemmas();
      if (confl != CRef_Undef) {
        return confl;
      }
    }

    // If this is the final check, no need for Boolean propagation and
    // theory propagation
    if (type == CHECK_FINAL) {
      // Do the theory check
      theoryCheck(CVC4::theory::Theory::EFFORT_FULL);
      // Pick up the theory propagated literals (there could be some,
      // if new lemmas are added)
      propagateTheory();
      // If there are lemmas (or conflicts) update them
      if (lemmas.size() > 0) {
        recheck = true;
        confl = updateLemmas();
        return confl;
      } else {
        recheck = d_proxy->theoryNeedCheck();
        return confl;
      }
    }

    // Keep running until we have checked everything, we
    // have no conflict and no new literals have been asserted
    do {
        // Propagate on the clauses
        confl = propagateBool();
        // If no conflict, do the theory check
        if (confl == CRef_Undef && type != CHECK_WITHOUT_THEORY) {
            // Do the theory check
            if (type == CHECK_FINAL_FAKE) {
              theoryCheck(CVC4::theory::Theory::EFFORT_FULL);
            } else {
              theoryCheck(CVC4::theory::Theory::EFFORT_STANDARD);
            }
            // Pick up the theory propagated literals
            propagateTheory();
            // If there are lemmas (or conflicts) update them
            if (lemmas.size() > 0) {
              confl = updateLemmas();
            }
        } else {
          // if dumping decision tree, print the conflict
          if (Trace.isOn("dtview::conflict"))
          {
            if (confl != CRef_Undef)
            {
              dtviewPropConflictHelper(decisionLevel(), ca[confl], d_proxy);
            }
          }
          // Even though in conflict, we still need to discharge the lemmas
          if (lemmas.size() > 0) {
            // Remember the trail size
            int oldLevel = decisionLevel();
            // Update the lemmas
            CRef lemmaConflict = updateLemmas();
            // If we get a conflict, we prefer it since it's earlier in the trail
            if (lemmaConflict != CRef_Undef) {
              // Lemma conflict takes precedence, since it's earlier in the trail
              confl = lemmaConflict;
            } else {
              // Otherwise, the Boolean conflict is canceled in the case we popped the trail
              if (oldLevel > decisionLevel()) {
                confl = CRef_Undef;
              }
            }
          }
        }
    } while (confl == CRef_Undef && qhead < trail.size());
    return confl;
}

void Solver::propagateTheory() {
  SatClause propagatedLiteralsClause;
  // Doesn't actually call propagate(); that's done in theoryCheck() now that combination
  // is online.  This just incorporates those propagations previously discovered.
  d_proxy->theoryPropagate(propagatedLiteralsClause);

  vec<Lit> propagatedLiterals;
  MinisatSatSolver::toMinisatClause(propagatedLiteralsClause, propagatedLiterals);

  int oldTrailSize = trail.size();
  Debug("minisat") << "old trail size is " << oldTrailSize << ", propagating " << propagatedLiterals.size() << " lits..." << std::endl;
  for (unsigned i = 0, i_end = propagatedLiterals.size(); i < i_end; ++ i) {
    Debug("minisat") << "Theory propagated: " << propagatedLiterals[i] << std::endl;
    // multiple theories can propagate the same literal
    Lit p = propagatedLiterals[i];
    if (value(p) == l_Undef) {
      uncheckedEnqueue(p, CRef_Lazy);
    } else {
      if (value(p) == l_False) {
        Debug("minisat") << "Conflict in theory propagation" << std::endl;
        SatClause explanation_cl;
        d_proxy->explainPropagation(MinisatSatSolver::toSatLiteral(p),
                                    explanation_cl);
        vec<Lit> explanation;
        MinisatSatSolver::toMinisatClause(explanation_cl, explanation);
        ClauseId id; // FIXME: mark it as explanation here somehow?
        addClause(explanation, true, id);
        // explainPropagation() pushes the explanation on the assertion
        // stack in CnfProof, so we need to pop it here.
        if (options::unsatCores())
        {
          ProofManager::getCnfProof()->popCurrentAssertion();
        }
      }
    }
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
  d_proxy->theoryCheck(effort);
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

        // if propagation tracing enabled, print boolean propagation
        if (Trace.isOn("dtview::prop"))
        {
          dtviewBoolPropagationHelper(decisionLevel(), p, d_proxy);
        }

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
        if (satisfied(c)) {
          if (options::unsatCores() && locked(c))
          {
            // store a resolution of the literal c propagated
            ProofManager::getSatProof()->storeUnitResolution(c[0]);
          }
            removeClause(cs[i]);
        }
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
            assert(!locked(c));
            removeClause(cs[i]);
        } else {
            cs[j++] = cs[i];
        }
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

    if (!ok || propagate(CHECK_WITHOUT_THEORY) != CRef_Undef)
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

    TheoryCheckType check_type = CHECK_WITH_THEORY;
    for (;;) {

        // Propagate and call the theory solvers
        CRef confl = propagate(check_type);
        Assert(lemmas.size() == 0);

        if (confl != CRef_Undef) {

            conflicts++; conflictC++;

            if (decisionLevel() == 0) {
              if (options::unsatCores())
              {
                ProofManager::getSatProof()->finalizeProof(confl);
              }
              return l_False;
            }

            // Analyze the conflict
            learnt_clause.clear();
            int max_level = analyze(confl, learnt_clause, backtrack_level);
            cancelUntil(backtrack_level);

            // Assert the conflict clause and the asserting literal
            if (learnt_clause.size() == 1) {
                uncheckedEnqueue(learnt_clause[0]);

                if (options::unsatCores())
                {
                  ProofManager::getSatProof()->endResChain(learnt_clause[0]);
                }
            } else {
              CRef cr =
                  ca.alloc(assertionLevelOnly() ? assertionLevel : max_level,
                           learnt_clause,
                           true);
              clauses_removable.push(cr);
              attachClause(cr);
              claBumpActivity(ca[cr]);
              uncheckedEnqueue(learnt_clause[0], cr);
              if (options::unsatCores())
              {
                ClauseId id =
                    ProofManager::getSatProof()->registerClause(cr, LEARNT);
                ProofManager::getSatProof()->endResChain(id);
              }
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

            if (theoryConflict && options::sat_refine_conflicts()) {
              check_type = CHECK_FINAL_FAKE;
            } else {
              check_type = CHECK_WITH_THEORY;
            }

        } else {
          // If this was a final check, we are satisfiable
          if (check_type == CHECK_FINAL)
          {
            bool decisionEngineDone = d_proxy->isDecisionEngineDone();
            // Unless a lemma has added more stuff to the queues
            if (!decisionEngineDone
                && (!order_heap.empty() || qhead < trail.size()))
            {
              check_type = CHECK_WITH_THEORY;
              continue;
            }
            else if (recheck)
            {
              // There some additional stuff added, so we go for another
              // full-check
              continue;
            }
            else
            {
              // Yes, we're truly satisfiable
              return l_True;
            }
          }
          else if (check_type == CHECK_FINAL_FAKE)
          {
            check_type = CHECK_WITH_THEORY;
          }

            if ((nof_conflicts >= 0 && conflictC >= nof_conflicts)
                || !withinBudget(ResourceManager::Resource::SatConflictStep))
            {
              // Reached bound on number of conflicts:
              progress_estimate = progressEstimate();
              cancelUntil(0);
              // [mdeters] notify theory engine of restarts for deferred
              // theory processing
              d_proxy->notifyRestart();
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
                  analyzeFinal(~p, d_conflict);
                  return l_False;
                } else {
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef) {
                // New variable decision:
                next = pickBranchLit();

                if (next == lit_Undef) {
                    // We need to do a full theory check to confirm
                  Debug("minisat::search") << "Doing a full theory check..."
                                           << std::endl;
                    check_type = CHECK_FINAL;
                    continue;
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
    Debug("minisat") << "nvars = " << nVars() << std::endl;

    ScopedBool scoped_bool(minisat_busy, true);

    assert(decisionLevel() == 0);

    model.clear();
    d_conflict.clear();
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
        if (!withinBudget(ResourceManager::Resource::SatConflictStep))
          break;  // FIXME add restart option?
        curr_restarts++;
    }

    if (!withinBudget(ResourceManager::Resource::SatConflictStep))
      status = l_Undef;

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) {
          model[i] = value(i);
          Debug("minisat") << i << " = " << model[i] << std::endl;
        }
    }
    else if (status == l_False && d_conflict.size() == 0)
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
              ca.reloc(ws[j].cref,
                       to,
                       CVC4::options::unsatCores() ? ProofManager::getSatProof()
                                                   : nullptr);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (hasReasonClause(v) && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
          ca.reloc(vardata[v].d_reason,
                   to,
                   CVC4::options::unsatCores() ? ProofManager::getSatProof()
                                               : nullptr);
    }
    // All learnt:
    //
    for (int i = 0; i < clauses_removable.size(); i++)
      ca.reloc(
          clauses_removable[i],
          to,
          CVC4::options::unsatCores() ? ProofManager::getSatProof() : nullptr);

    // All original:
    //
    for (int i = 0; i < clauses_persistent.size(); i++)
      ca.reloc(
          clauses_persistent[i],
          to,
          CVC4::options::unsatCores() ? ProofManager::getSatProof() : nullptr);

    if (options::unsatCores())
    {
      ProofManager::getSatProof()->finishUpdateCRef();
    }
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
  assert(d_enable_incremental);
  assert(decisionLevel() == 0);

  ++assertionLevel;
  Debug("minisat") << "in user push, increasing assertion level to " << assertionLevel << std::endl;
  trail_ok.push(ok);
  assigns_lim.push(assigns.size());

  d_context->push();  // SAT context for CVC4

  Debug("minisat") << "MINISAT PUSH assertionLevel is " << assertionLevel << ", trail.size is " << trail.size() << std::endl;
}

void Solver::pop()
{
  assert(d_enable_incremental);

  assert(decisionLevel() == 0);

  // Pop the trail below the user level
  --assertionLevel;
  while (true) {
    Debug("minisat") << "== unassigning " << trail.last() << std::endl;
    Var      x  = var(trail.last());
    if (user_level(x) > assertionLevel) {
      assigns[x] = l_Undef;
      vardata[x] = VarData(CRef_Undef, -1, -1, intro_level(x), -1);
      if(phase_saving >= 1 && (polarity[x] & 0x2) == 0)
        polarity[x] = sign(trail.last());
      insertVarOrder(x);
      trail.pop();
    } else {
      break;
    }
  }
  // The head should be at the trail top
  qhead = trail.size();

  // Remove the clauses
  removeClausesAboveLevel(clauses_persistent, assertionLevel);
  removeClausesAboveLevel(clauses_removable, assertionLevel);

  // Pop the SAT context to notify everyone
  d_context->pop();  // SAT context for CVC4

  // Pop the created variables
  resizeVars(assigns_lim.last());
  assigns_lim.pop();
  variables_to_register.clear();

  // Pop the OK
  ok = trail_ok.last();
  trail_ok.pop();
}

CRef Solver::updateLemmas() {

  Debug("minisat::lemmas") << "Solver::updateLemmas() begin" << std::endl;

  // Avoid adding lemmas indefinitely without resource-out
  d_proxy->spendResource(ResourceManager::Resource::LemmaStep);

  CRef conflict = CRef_Undef;

  // Decision level to backtrack to
  int backtrackLevel = decisionLevel();

  // We use this comparison operator
  lemma_lt lt(*this);

  // Check for propagation and level to backtrack to
  int i = 0;
  while (i < lemmas.size()) {
    // We need this loop as when we backtrack, due to registration more lemmas could be added
    for (; i < lemmas.size(); ++ i)
    {
      // The current lemma
      vec<Lit>& lemma = lemmas[i];

      Debug("pf::sat") << "Solver::updateLemmas: working on lemma: ";
      for (int k = 0; k < lemma.size(); ++k) {
        Debug("pf::sat") << lemma[k] << " ";
      }
      Debug("pf::sat") << std::endl;

      // If it's an empty lemma, we have a conflict at zero level
      if (lemma.size() == 0) {
        Assert(!options::unsatCores());
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
  }

  // Last index in the trail
  int backtrack_index = trail.size();

  Assert(!options::unsatCores()
         || lemmas.size() == (int)lemmas_cnf_assertion.size());

  // Attach all the clauses and enqueue all the propagations
  for (int j = 0; j < lemmas.size(); ++j)
  {
    // The current lemma
    vec<Lit>& lemma = lemmas[j];
    bool removable = lemmas_removable[j];

    // Attach it if non-unit
    CRef lemma_ref = CRef_Undef;
    if (lemma.size() > 1) {
      // If the lemmas is removable, we can compute its level by the level
      int clauseLevel = assertionLevel;
      if (removable && !assertionLevelOnly())
      {
        clauseLevel = 0;
        for (int k = 0; k < lemma.size(); ++k)
        {
          clauseLevel = std::max(clauseLevel, intro_level(var(lemma[k])));
        }
      }

      lemma_ref = ca.alloc(clauseLevel, lemma, removable);
      if (options::unsatCores())
      {
        TNode cnf_assertion = lemmas_cnf_assertion[j];

        Debug("pf::sat") << "Minisat::Solver registering a THEORY_LEMMA (2)"
                         << std::endl;
        ClauseId id = ProofManager::getSatProof()->registerClause(lemma_ref,
                                                                  THEORY_LEMMA);
        ProofManager::getCnfProof()->setClauseAssertion(id, cnf_assertion);
      }
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
        if (options::unsatCores() && lemma.size() == 1)
        {
          Node cnf_assertion = lemmas_cnf_assertion[j];

          Debug("pf::sat") << "Minisat::Solver registering a THEORY_LEMMA (3) "
                           << cnf_assertion << value(lemma[0]) << std::endl;
          ClauseId id = ProofManager::getSatProof()->registerUnitClause(
              lemma[0], THEORY_LEMMA);
          ProofManager::getCnfProof()->setClauseAssertion(id, cnf_assertion);
        }

        if (value(lemma[0]) == l_False) {
          // We have a conflict
          if (lemma.size() > 1) {
            Debug("minisat::lemmas") << "Solver::updateLemmas(): conflict" << std::endl;
            conflict = lemma_ref;
          } else {
            Debug("minisat::lemmas") << "Solver::updateLemmas(): unit conflict or empty clause" << std::endl;
            conflict = CRef_Lazy;
            if (options::unsatCores())
            {
              ProofManager::getSatProof()->storeUnitConflict(lemma[0], LEARNT);
            }
          }
        } else {
          Debug("minisat::lemmas") << "lemma size is " << lemma.size() << std::endl;
          uncheckedEnqueue(lemma[0], lemma_ref);
        }
      }
    }
  }

  Assert(!options::unsatCores()
         || lemmas.size() == (int)lemmas_cnf_assertion.size());
  // Clear the lemmas
  lemmas.clear();
  lemmas_cnf_assertion.clear();
  lemmas_removable.clear();

  if (conflict != CRef_Undef) {
    theoryConflict = true;
  }

  Debug("minisat::lemmas") << "Solver::updateLemmas() end" << std::endl;

  return conflict;
}

void ClauseAllocator::reloc(CRef& cr,
                            ClauseAllocator& to,
                            CVC4::TSatProof<Solver>* proof)
{

  // FIXME what is this CRef_lazy
  if (cr == CRef_Lazy) return;

  CRef old = cr;  // save the old reference
  Clause& c = operator[](cr);
  if (c.reloced()) { cr = c.relocation(); return; }

  cr = to.alloc(c.level(), c, c.removable());
  c.relocate(cr);
  if (proof)
  {
    proof->updateCRef(old, cr);
  }
  // Copy extra data-fields:
  // (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
  to[cr].mark(c.mark());
  if (to[cr].removable())         to[cr].activity() = c.activity();
  else if (to[cr].has_extra()) to[cr].calcAbstraction();
}

inline bool Solver::withinBudget(ResourceManager::Resource r) const
{
  Assert(d_proxy);
  // spendResource sets async_interrupt or throws UnsafeInterruptException
  // depending on whether hard-limit is enabled
  d_proxy->spendResource(r);

  bool within_budget =
      !asynch_interrupt
      && (conflict_budget < 0 || conflicts < (uint64_t)conflict_budget)
      && (propagation_budget < 0
          || propagations < (uint64_t)propagation_budget);
  return within_budget;
}

} /* CVC4::Minisat namespace */
} /* CVC4 namespace */

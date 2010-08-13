/************************************************************************************[SimpSolver.C]
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

#include "Sort.h"
#include "SimpSolver.h"


//=================================================================================================
// Constructor/Destructor:


SimpSolver::SimpSolver() :
    grow               (0)
  , asymm_mode         (false)
  , redundancy_check   (false)
  , merges             (0)
  , asymm_lits         (0)
  , remembered_clauses (0)
  , elimorder          (1)
  , use_simplification (true)
  , elim_heap          (ElimLt(n_occ))
  , bwdsub_assigns     (0)
{
    vec<Lit> dummy(1,lit_Undef);
    bwdsub_tmpunit   = Clause_new(dummy);
    remove_satisfied = false;
}


SimpSolver::~SimpSolver()
{
    free(bwdsub_tmpunit);

    // NOTE: elimtable.size() might be lower than nVars() at the moment
    for (int i = 0; i < elimtable.size(); i++)
        for (int j = 0; j < elimtable[i].eliminated.size(); j++)
            free(elimtable[i].eliminated[j]);
}


Var SimpSolver::newVar(bool sign, bool dvar) {
    Var v = Solver::newVar(sign, dvar);

    if (use_simplification){
        n_occ    .push(0);
        n_occ    .push(0);
        occurs   .push();
        frozen   .push((char)false);
        touched  .push(0);
        elim_heap.insert(v);
        elimtable.push();
    }
    return v; }



bool SimpSolver::solve(const vec<Lit>& assumps, bool do_simp, bool turn_off_simp) {
    vec<Var> extra_frozen;
    bool     result = true;

    do_simp &= use_simplification;

    if (do_simp){
        // Assumptions must be temporarily frozen to run variable elimination:
        for (int i = 0; i < assumps.size(); i++){
            Var v = var(assumps[i]);

            // If an assumption has been eliminated, remember it.
            if (isEliminated(v))
                remember(v);

            if (!frozen[v]){
                // Freeze and store.
                setFrozen(v, true);
                extra_frozen.push(v);
            } }

        result = eliminate(turn_off_simp);
    }

    if (result)
        result = Solver::solve(assumps);

    if (result) {
        extendModel();
#ifndef NDEBUG
        verifyModel();
#endif
    }

    if (do_simp)
        // Unfreeze the assumptions that were frozen:
        for (int i = 0; i < extra_frozen.size(); i++)
            setFrozen(extra_frozen[i], false);

    return result;
}



bool SimpSolver::addClause(vec<Lit>& ps)
{
    for (int i = 0; i < ps.size(); i++)
        if (isEliminated(var(ps[i])))
            remember(var(ps[i]));

    int nclauses = clauses.size();

    if (redundancy_check && implied(ps))
        return true;

    if (!Solver::addClause(ps))
        return false;

    if (use_simplification && clauses.size() == nclauses + 1){
        Clause& c = *clauses.last();

        subsumption_queue.insert(&c);

        for (int i = 0; i < c.size(); i++){
            assert(occurs.size() > var(c[i]));
            assert(!find(occurs[var(c[i])], &c));

            occurs[var(c[i])].push(&c);
            n_occ[toInt(c[i])]++;
            touched[var(c[i])] = 1;
            assert(elimtable[var(c[i])].order == 0);
            if (elim_heap.inHeap(var(c[i])))
                elim_heap.increase_(var(c[i]));
        }
    }

    return true;
}


void SimpSolver::removeClause(Clause& c)
{
    assert(!c.learnt());

    if (use_simplification)
        for (int i = 0; i < c.size(); i++){
            n_occ[toInt(c[i])]--;
            updateElimHeap(var(c[i]));
        }

    detachClause(c);
    c.mark(1);
}


bool SimpSolver::strengthenClause(Clause& c, Lit l)
{
    assert(decisionLevel() == 0);
    assert(c.mark() == 0);
    assert(!c.learnt());
    assert(find(watches[toInt(~c[0])], &c));
    assert(find(watches[toInt(~c[1])], &c));

    // FIX: this is too inefficient but would be nice to have (properly implemented)
    // if (!find(subsumption_queue, &c))
    subsumption_queue.insert(&c);

    // If l is watched, delete it from watcher list and watch a new literal
    if (c[0] == l || c[1] == l){
        Lit other = c[0] == l ? c[1] : c[0];
        if (c.size() == 2){
            removeClause(c);
            c.strengthen(l);
        }else{
            c.strengthen(l);
            remove(watches[toInt(~l)], &c);

            // Add a watch for the correct literal
            watches[toInt(~(c[1] == other ? c[0] : c[1]))].push(&c);

            // !! this version assumes that remove does not change the order !!
            //watches[toInt(~c[1])].push(&c);
            clauses_literals -= 1;
        }
    }
    else{
        c.strengthen(l);
        clauses_literals -= 1;
    }

    // if subsumption-indexing is active perform the necessary updates
    if (use_simplification){
        remove(occurs[var(l)], &c);
        n_occ[toInt(l)]--;
        updateElimHeap(var(l));
    }

    return c.size() == 1 ? enqueue(c[0]) && propagate() == NULL : true;
}


// Returns FALSE if clause is always satisfied ('out_clause' should not be used).
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v, vec<Lit>& out_clause)
{
    merges++;
    out_clause.clear();

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps =  ps_smallest ? _qs : _ps;
    const Clause& qs =  ps_smallest ? _ps : _qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(ps[j]) == var(qs[i]))
                    if (ps[j] == ~qs[i])
                        return false;
                    else
                        goto next;
            out_clause.push(qs[i]);
        }
        next:;
    }

    for (int i = 0; i < ps.size(); i++)
        if (var(ps[i]) != v)
            out_clause.push(ps[i]);

    return true;
}


// Returns FALSE if clause is always satisfied.
bool SimpSolver::merge(const Clause& _ps, const Clause& _qs, Var v)
{
    merges++;

    bool  ps_smallest = _ps.size() < _qs.size();
    const Clause& ps =  ps_smallest ? _qs : _ps;
    const Clause& qs =  ps_smallest ? _ps : _qs;
    const Lit* __ps = (const Lit*)ps;
    const Lit* __qs = (const Lit*)qs;

    for (int i = 0; i < qs.size(); i++){
        if (var(__qs[i]) != v){
            for (int j = 0; j < ps.size(); j++)
                if (var(__ps[j]) == var(__qs[i]))
                    if (__ps[j] == ~__qs[i])
                        return false;
                    else
                        goto next;
        }
        next:;
    }

    return true;
}


void SimpSolver::gatherTouchedClauses()
{
    //fprintf(stderr, "Gathering clauses for backwards subsumption\n");
    int ntouched = 0;
    for (int i = 0; i < touched.size(); i++)
        if (touched[i]){
            const vec<Clause*>& cs = getOccurs(i);
            ntouched++;
            for (int j = 0; j < cs.size(); j++)
                if (cs[j]->mark() == 0){
                    subsumption_queue.insert(cs[j]);
                    cs[j]->mark(2);
                }
            touched[i] = 0;
        }

    //fprintf(stderr, "Touched variables %d of %d yields %d clauses to check\n", ntouched, touched.size(), clauses.size());
    for (int i = 0; i < subsumption_queue.size(); i++)
        subsumption_queue[i]->mark(0);
}


bool SimpSolver::implied(const vec<Lit>& c)
{
    assert(decisionLevel() == 0);

    trail_lim.push(trail.size());
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True){
            cancelUntil(0);
            return false;
        }else if (value(c[i]) != l_False){
            assert(value(c[i]) == l_Undef);
            uncheckedEnqueue(~c[i]);
        }

    bool result = propagate() != NULL;
    cancelUntil(0);
    return result;
}


// Backward subsumption + backward subsumption resolution
bool SimpSolver::backwardSubsumptionCheck(bool verbose)
{
    int cnt = 0;
    int subsumed = 0;
    int deleted_literals = 0;
    assert(decisionLevel() == 0);

    while (subsumption_queue.size() > 0 || bwdsub_assigns < trail.size()){

        // Check top-level assignments by creating a dummy clause and placing it in the queue:
        if (subsumption_queue.size() == 0 && bwdsub_assigns < trail.size()){
            Lit l = trail[bwdsub_assigns++];
            (*bwdsub_tmpunit)[0] = l;
            bwdsub_tmpunit->calcAbstraction();
            assert(bwdsub_tmpunit->mark() == 0);
            subsumption_queue.insert(bwdsub_tmpunit); }

        Clause&  c = *subsumption_queue.peek(); subsumption_queue.pop();

        if (c.mark()) continue;

        if (verbose && verbosity >= 2 && cnt++ % 1000 == 0)
            reportf("subsumption left: %10d (%10d subsumed, %10d deleted literals)\r", subsumption_queue.size(), subsumed, deleted_literals);

        assert(c.size() > 1 || value(c[0]) == l_True);    // Unit-clauses should have been propagated before this point.

        // Find best variable to scan:
        Var best = var(c[0]);
        for (int i = 1; i < c.size(); i++)
            if (occurs[var(c[i])].size() < occurs[best].size())
                best = var(c[i]);

        // Search all candidates:
        vec<Clause*>& _cs = getOccurs(best);
        Clause**       cs = (Clause**)_cs;

        for (int j = 0; j < _cs.size(); j++)
            if (c.mark())
                break;
            else if (!cs[j]->mark() && cs[j] != &c){
                Lit l = c.subsumes(*cs[j]);

                if (l == lit_Undef)
                    subsumed++, removeClause(*cs[j]);
                else if (l != lit_Error){
                    deleted_literals++;

                    if (!strengthenClause(*cs[j], ~l))
                        return false;

                    // Did current candidate get deleted from cs? Then check candidate at index j again:
                    if (var(l) == best)
                        j--;
                }
            }
    }

    return true;
}


bool SimpSolver::asymm(Var v, Clause& c)
{
    assert(decisionLevel() == 0);

    if (c.mark() || satisfied(c)) return true;

    trail_lim.push(trail.size());
    Lit l = lit_Undef;
    for (int i = 0; i < c.size(); i++)
        if (var(c[i]) != v && value(c[i]) != l_False)
            uncheckedEnqueue(~c[i]);
        else
            l = c[i];

    if (propagate() != NULL){
        cancelUntil(0);
        asymm_lits++;
        if (!strengthenClause(c, l))
            return false;
    }else
        cancelUntil(0);

    return true;
}


bool SimpSolver::asymmVar(Var v)
{
    assert(!frozen[v]);
    assert(use_simplification);

    vec<Clause*>  pos, neg;
    const vec<Clause*>& cls = getOccurs(v);

    if (value(v) != l_Undef || cls.size() == 0)
        return true;

    for (int i = 0; i < cls.size(); i++)
        if (!asymm(v, *cls[i]))
            return false;

    return backwardSubsumptionCheck();
}


void SimpSolver::verifyModel()
{
    bool failed = false;
    int  cnt    = 0;
    // NOTE: elimtable.size() might be lower than nVars() at the moment
    for (int i = 0; i < elimtable.size(); i++)
        if (elimtable[i].order > 0)
            for (int j = 0; j < elimtable[i].eliminated.size(); j++){
                cnt++;
                Clause& c = *elimtable[i].eliminated[j];
                for (int k = 0; k < c.size(); k++)
                    if (modelValue(c[k]) == l_True)
                        goto next;

                reportf("unsatisfied clause: ");
                printClause(*elimtable[i].eliminated[j]);
                reportf("\n");
                failed = true;
            next:;
            }

    assert(!failed);
    reportf("Verified %d eliminated clauses.\n", cnt);
}


bool SimpSolver::eliminateVar(Var v, bool fail)
{
    if (!fail && asymm_mode && !asymmVar(v))    return false;

    const vec<Clause*>& cls = getOccurs(v);

//  if (value(v) != l_Undef || cls.size() == 0) return true;
    if (value(v) != l_Undef) return true;

    // Split the occurrences into positive and negative:
    vec<Clause*>  pos, neg;
    for (int i = 0; i < cls.size(); i++)
        (find(*cls[i], Lit(v)) ? pos : neg).push(cls[i]);

    // Check if number of clauses decreases:
    int cnt = 0;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(*pos[i], *neg[j], v) && ++cnt > cls.size() + grow)
                return true;

    // Delete and store old clauses:
    setDecisionVar(v, false);
    elimtable[v].order = elimorder++;
    assert(elimtable[v].eliminated.size() == 0);
    for (int i = 0; i < cls.size(); i++){
        elimtable[v].eliminated.push(Clause_new(*cls[i]));
        removeClause(*cls[i]); }

    // Produce clauses in cross product:
    int top = clauses.size();
    vec<Lit> resolvent;
    for (int i = 0; i < pos.size(); i++)
        for (int j = 0; j < neg.size(); j++)
            if (merge(*pos[i], *neg[j], v, resolvent) && !addClause(resolvent))
                return false;

    // DEBUG: For checking that a clause set is saturated with respect to variable elimination.
    //        If the clause set is expected to be saturated at this point, this constitutes an
    //        error.
    if (fail){
        reportf("eliminated var %d, %d <= %d\n", v+1, cnt, cls.size());
        reportf("previous clauses:\n");
        for (int i = 0; i < cls.size(); i++){
            printClause(*cls[i]); reportf("\n"); }
        reportf("new clauses:\n");
        for (int i = top; i < clauses.size(); i++){
            printClause(*clauses[i]); reportf("\n"); }
        assert(0); }

    return backwardSubsumptionCheck();
}


void SimpSolver::remember(Var v)
{
    assert(decisionLevel() == 0);
    assert(isEliminated(v));

    vec<Lit> clause;

    // Re-activate variable:
    elimtable[v].order = 0;
    setDecisionVar(v, true); // Not good if the variable wasn't a decision variable before. Not sure how to fix this right now.

    if (use_simplification)
        updateElimHeap(v);

    // Reintroduce all old clauses which may implicitly remember other clauses:
    for (int i = 0; i < elimtable[v].eliminated.size(); i++){
        Clause& c = *elimtable[v].eliminated[i];
        clause.clear();
        for (int j = 0; j < c.size(); j++)
            clause.push(c[j]);

        remembered_clauses++;
        check(addClause(clause));
        free(&c);
    }

    elimtable[v].eliminated.clear();
}


void SimpSolver::extendModel()
{
    vec<Var> vs;

    // NOTE: elimtable.size() might be lower than nVars() at the moment
    for (int v = 0; v < elimtable.size(); v++)
        if (elimtable[v].order > 0)
            vs.push(v);

    sort(vs, ElimOrderLt(elimtable));

    for (int i = 0; i < vs.size(); i++){
        Var v = vs[i];
        Lit l = lit_Undef;

        for (int j = 0; j < elimtable[v].eliminated.size(); j++){
            Clause& c = *elimtable[v].eliminated[j];

            for (int k = 0; k < c.size(); k++)
                if (var(c[k]) == v)
                    l = c[k];
                else if (modelValue(c[k]) != l_False)
                    goto next;

            assert(l != lit_Undef);
            model[v] = lbool(!sign(l));
            break;

        next:;
        }

        if (model[v] == l_Undef)
            model[v] = l_True;
    }
}


bool SimpSolver::eliminate(bool turn_off_elim)
{
    if (!ok || !use_simplification)
        return ok;

    // Main simplification loop:
    //assert(subsumption_queue.size() == 0);
    //gatherTouchedClauses();
    while (subsumption_queue.size() > 0 || elim_heap.size() > 0){

        //fprintf(stderr, "subsumption phase: (%d)\n", subsumption_queue.size());
        if (!backwardSubsumptionCheck(true))
            return false;

        //fprintf(stderr, "elimination phase:\n (%d)", elim_heap.size());
        for (int cnt = 0; !elim_heap.empty(); cnt++){
            Var elim = elim_heap.removeMin();

            if (verbosity >= 2 && cnt % 100 == 0)
                reportf("elimination left: %10d\r", elim_heap.size());

            if (!frozen[elim] && !eliminateVar(elim))
                return false;
        }

        assert(subsumption_queue.size() == 0);
        gatherTouchedClauses();
    }

    // Cleanup:
    cleanUpClauses();
    order_heap.filter(VarFilter(*this));

#ifdef INVARIANTS
    // Check that no more subsumption is possible:
    reportf("Checking that no more subsumption is possible\n");
    for (int i = 0; i < clauses.size(); i++){
        if (i % 1000 == 0)
            reportf("left %10d\r", clauses.size() - i);

        assert(clauses[i]->mark() == 0);
        for (int j = 0; j < i; j++)
            assert(clauses[i]->subsumes(*clauses[j]) == lit_Error);
    }
    reportf("done.\n");

    // Check that no more elimination is possible:
    reportf("Checking that no more elimination is possible\n");
    for (int i = 0; i < nVars(); i++)
        if (!frozen[i]) eliminateVar(i, true);
    reportf("done.\n");
    checkLiteralCount();
#endif

    // If no more simplification is needed, free all simplification-related data structures:
    if (turn_off_elim){
        use_simplification = false;
        touched.clear(true);
        occurs.clear(true);
        n_occ.clear(true);
        subsumption_queue.clear(true);
        elim_heap.clear(true);
        remove_satisfied = true;
    }


    return true;
}


void SimpSolver::cleanUpClauses()
{
    int      i , j;
    vec<Var> dirty;
    for (i = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 1){
            Clause& c = *clauses[i];
            for (int k = 0; k < c.size(); k++)
                if (!seen[var(c[k])]){
                    seen[var(c[k])] = 1;
                    dirty.push(var(c[k]));
                } }

    for (i = 0; i < dirty.size(); i++){
        cleanOcc(dirty[i]);
        seen[dirty[i]] = 0; }

    for (i = j = 0; i < clauses.size(); i++)
        if (clauses[i]->mark() == 1)
            free(clauses[i]);
        else
            clauses[j++] = clauses[i];
    clauses.shrink(i - j);
}


//=================================================================================================
// Convert to DIMACS:


void SimpSolver::toDimacs(FILE* f, Clause& c)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", var(c[i])+1);
    fprintf(f, "0\n");
}


void SimpSolver::toDimacs(const char* file)
{
    assert(decisionLevel() == 0);
    FILE* f = fopen(file, "wr");
    if (f != NULL){

        // Cannot use removeClauses here because it is not safe
        // to deallocate them at this point. Could be improved.
        int cnt = 0;
        for (int i = 0; i < clauses.size(); i++)
            if (!satisfied(*clauses[i]))
                cnt++;

        fprintf(f, "p cnf %d %d\n", nVars(), cnt);

        for (int i = 0; i < clauses.size(); i++)
            toDimacs(f, *clauses[i]);

        fprintf(stderr, "Wrote %d clauses...\n", clauses.size());
    }else
        fprintf(stderr, "could not open file %s\n", file);
}

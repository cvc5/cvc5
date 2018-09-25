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

#include <iostream>
#include <vector>
#include <iomanip>

#include "solvertypes.h"
#include "sccfinder.h"
#include "varreplacer.h"
#include "time_mem.h"
#include "solver.h"
#include "sqlstats.h"

using namespace CMSat;
using std::cout;
using std::endl;

SCCFinder::SCCFinder(Solver* _solver) :
    globalIndex(0)
    , solver(_solver)
{}

bool SCCFinder::performSCC(uint64_t* bogoprops_given)
{
    assert(binxors.empty());
    runStats.clear();
    runStats.numCalls = 1;
    depth_warning_issued = false;
    const double myTime = cpuTime();

    globalIndex = 0;
    index.clear();
    index.resize(solver->nVars()*2, std::numeric_limits<uint32_t>::max());
    lowlink.clear();
    lowlink.resize(solver->nVars()*2, std::numeric_limits<uint32_t>::max());
    stackIndicator.clear();
    stackIndicator.resize(solver->nVars()*2, false);
    assert(stack.empty());

    depth = 0;
    for (uint32_t vertex = 0; vertex < solver->nVars()*2; vertex++) {
        //Start a DFS at each node we haven't visited yet
        const uint32_t v = vertex>>1;
        if (solver->value(v) != l_Undef) {
            continue;
        }
        assert(depth == 0);
        if (index[vertex] == std::numeric_limits<uint32_t>::max()) {
            tarjan(vertex);
            depth--;
            assert(stack.empty());
        }
    }

    //Update & print stats
    runStats.cpu_time = cpuTime() - myTime;
    runStats.foundXorsNew = binxors.size();
    if (solver->conf.verbosity) {
        if (solver->conf.verbosity >= 3)
            runStats.print();
        else
            runStats.print_short(solver);
    }
    globalStats += runStats;

    if (bogoprops_given) {
        *bogoprops_given += runStats.bogoprops;
    }

    return solver->okay();
}

void SCCFinder::tarjan(const uint32_t vertex)
{
    depth++;
    if (depth >= (uint32_t)solver->conf.max_scc_depth) {
        if (solver->conf.verbosity && !depth_warning_issued) {
            depth_warning_issued = true;
            cout << "c [scc] WARNING: reached maximum depth of " << solver->conf.max_scc_depth << endl;
        }
        return;
    }

    const Lit vertLit = Lit::toLit(vertex);
    if (solver->varData[vertLit.var()].removed != Removed::none) {
        return;
    }

    runStats.bogoprops += 1;
    index[vertex] = globalIndex;  // Set the depth index for v
    lowlink[vertex] = globalIndex;
    globalIndex++;
    stack.push(vertex); // Push v on the stack
    stackIndicator[vertex] = true;

    vector<LitExtra>* transCache = NULL;
    if (solver->conf.doCache
        && solver->conf.doExtendedSCC
        && (!(solver->drat->enabled() || solver->conf.simulate_drat) ||
            solver->conf.otfHyperbin)
    ) {
        transCache = &(solver->implCache[~vertLit].lits);
        __builtin_prefetch(transCache->data());
    }

    //Go through the watch
    watch_subarray_const ws = solver->watches[~vertLit];
    runStats.bogoprops += ws.size()/4;
    for (const Watched& w: ws) {
        //Only binary clauses matter
        if (!w.isBin())
            continue;

        const Lit lit = w.lit2();
        if (solver->value(lit) != l_Undef) {
            continue;
        }
        doit(lit, vertex);
    }

    if (transCache) {
        runStats.bogoprops += transCache->size()/4;
        for (const LitExtra& le: *transCache) {
            Lit lit = le.getLit();
            if (solver->value(lit) != l_Undef) {
                continue;
            }
            if (lit != ~vertLit) {
                doit(lit, vertex);
            }
        }
    }

    // Is v the root of an SCC?
    if (lowlink[vertex] == index[vertex]) {
        uint32_t vprime;
        tmp.clear();
        do {
            assert(!stack.empty());
            vprime = stack.top();
            stack.pop();
            stackIndicator[vprime] = false;
            tmp.push_back(vprime);
        } while (vprime != vertex);
        if (tmp.size() >= 2) {
            runStats.bogoprops += 3;
            add_bin_xor_in_tmp();
        }
    }
}

void SCCFinder::add_bin_xor_in_tmp()
{
    for (uint32_t i = 1; i < tmp.size(); i++) {
        bool rhs = Lit::toLit(tmp[0]).sign()
            ^ Lit::toLit(tmp[i]).sign();

        BinaryXor binxor(Lit::toLit(tmp[0]).var(), Lit::toLit(tmp[i]).var(), rhs);
        binxors.insert(binxor);

        //Both are UNDEF, so this is a proper binary XOR
        if (solver->value(binxor.vars[0]) == l_Undef
            && solver->value(binxor.vars[1]) == l_Undef
        ) {
            runStats.foundXors++;
            #ifdef VERBOSE_DEBUG
            cout << "SCC says: "
            << binxor.vars[0] +1
            << " XOR "
            << binxor.vars[1] +1
            << " = " << binxor.rhs
            << endl;
            #endif
        }
    }
}

void SCCFinder::Stats::print_short(Solver* solver) const
{
    cout
    << "c [scc]"
    << " new: " << foundXorsNew
    << " BP " << bogoprops/(1000*1000) << "M";
    if (solver) {
        cout << solver->conf.print_times(cpu_time);
    } else {
        cout << "  T: " << std::setprecision(2) << std::fixed << cpu_time;
    }
    cout << endl;

    if (solver && solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "scc"
            , cpu_time
        );
    }
}

size_t SCCFinder::mem_used() const
{
    size_t mem = 0;
    mem += index.capacity()*sizeof(uint32_t);
    mem += lowlink.capacity()*sizeof(uint32_t);
    mem += stack.size()*sizeof(uint32_t); //TODO under-estimates
    mem += stackIndicator.capacity()*sizeof(char);
    mem += tmp.capacity()*sizeof(uint32_t);

    return mem;
}

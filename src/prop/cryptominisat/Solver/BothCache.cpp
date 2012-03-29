/***************************************************************************
CryptoMiniSat -- Copyright (c) 2010 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
*****************************************************************************/

#include "BothCache.h"
#include "time_mem.h"
#include <iomanip>
#include "VarReplacer.h"
#include "Subsumer.h"
#include "XorSubsumer.h"

namespace CMSat {

BothCache::BothCache(Solver& _solver) :
    solver(_solver)
{}

bool BothCache::tryBoth()
{
    vec<bool> seen(solver.nVars(), 0);
    vec<bool> val(solver.nVars(), 0);
    vec<Lit> tmp;
    uint32_t bProp = 0;
    uint32_t bXProp = 0;
    double myTime = cpuTime();
    uint32_t backupTrailSize = solver.trail.size();

    for (Var var = 0; var < solver.nVars(); var++) {
        if (solver.value(var) != l_Undef
            || solver.subsumer->getVarElimed()[var]
            || solver.xorSubsumer->getVarElimed()[var]
            || solver.varReplacer->getReplaceTable()[var].var() != var)
            continue;

        Lit lit = Lit(var, false);
        vector<Lit> const* cache1;
        vector<Lit> const* cache2;

        bool startWithTrue;
        if (solver.transOTFCache[lit.toInt()].lits.size() < solver.transOTFCache[(~lit).toInt()].lits.size()) {
            cache1 = &solver.transOTFCache[lit.toInt()].lits;
            cache2 = &solver.transOTFCache[(~lit).toInt()].lits;
            startWithTrue = false;
        } else {
            cache1 = &solver.transOTFCache[(~lit).toInt()].lits;
            cache2 = &solver.transOTFCache[lit.toInt()].lits;
            startWithTrue = true;
        }

        if (cache1->size() == 0) continue;

        for (vector<Lit>::const_iterator it = cache1->begin(), end = cache1->end(); it != end; it++) {
            seen[it->var()] = true;
            val[it->var()] = it->sign();
        }

        for (vector<Lit>::const_iterator it = cache2->begin(), end = cache2->end(); it != end; it++) {
            if (seen[it->var()]) {
                Var var2 = it->var();
                if (solver.subsumer->getVarElimed()[var2]
                    || solver.xorSubsumer->getVarElimed()[var2]
                    || solver.varReplacer->getReplaceTable()[var2].var() != var2)
                    continue;

                if  (val[it->var()] == it->sign()) {
                    tmp.clear();
                    tmp.push(*it);
                    solver.addClauseInt(tmp, true);
                    if  (!solver.ok) goto end;
                    bProp++;
                } else {
                    tmp.clear();
                    tmp.push(Lit(var, false));
                    tmp.push(Lit(it->var(), false));
                    bool sign = true ^ startWithTrue ^ it->sign();
                    solver.addXorClauseInt(tmp, sign);
                    if  (!solver.ok) goto end;
                    bXProp++;
                }
            }
        }

        for (vector<Lit>::const_iterator it = cache1->begin(), end = cache1->end(); it != end; it++) {
            seen[it->var()] = false;
        }
    }

    end:
    if (solver.conf.verbosity >= 1) {
        std::cout << "c Cache " <<
        " BProp: " << bProp <<
        " Set: " << (solver.trail.size() - backupTrailSize) <<
        " BXProp: " << bXProp <<
        " T: " << (cpuTime() - myTime) <<
        std::endl;
    }

    return solver.ok;
}

}

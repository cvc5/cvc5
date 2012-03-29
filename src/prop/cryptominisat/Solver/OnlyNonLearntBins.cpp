/***********************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

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
************************************************************************/

#include "OnlyNonLearntBins.h"

#include <iomanip>
#include "Solver.h"
#include "Clause.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"

using namespace CMSat;

OnlyNonLearntBins::OnlyNonLearntBins(Solver& _solver) :
    solver(_solver)
{}

/**
@brief Propagate recursively on non-learnt binaries
*/
bool OnlyNonLearntBins::propagate()
{
    while (solver.qhead < solver.trail.size()) {
        Lit p = solver.trail[solver.qhead++];
        vec<WatchedBin> & wbin = binwatches[p.toInt()];
        solver.propagations += wbin.size()/2 + 2;
        for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
            lbool val = solver.value(k->impliedLit);
            if (val.isUndef()) {
                solver.uncheckedEnqueueLight(k->impliedLit);
            } else if (val == l_False) {
                return false;
            }
        }
    }

    return true;
}

/**
@brief Fill internal watchlists with non-binary clauses
*/
bool OnlyNonLearntBins::fill()
{
    uint32_t numBins = 0;
    double myTime = cpuTime();
    binwatches.growTo(solver.nVars()*2);

    uint32_t wsLit = 0;
    for (const vec<Watched> *it = solver.watches.getData(), *end = solver.watches.getDataEnd(); it != end; it++, wsLit++) {
        const vec<Watched>& ws = *it;
        for (vec<Watched>::const_iterator it2 = ws.getData(), end2 = ws.getDataEnd(); it2 != end2; it2++) {
            if (it2->isBinary() && !it2->getLearnt()) {
                binwatches[wsLit].push(WatchedBin(it2->getOtherLit()));
                numBins++;
            }
        }
    }

    if (solver.conf.verbosity >= 3) {
        std::cout << "c Time to fill non-learnt binary watchlists:"
        << std::fixed << std::setprecision(2) << std::setw(5)
        << cpuTime() - myTime << " s"
        << " num non-learnt bins: " << std::setw(10) << numBins
        << std::endl;
    }

    return true;
}

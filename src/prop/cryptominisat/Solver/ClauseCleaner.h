/***********************************************************************************
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
**************************************************************************************************/

#ifndef CLAUSECLEANER_H
#define CLAUSECLEANER_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Solver.h"
#include "Subsumer.h"
#include "XorSubsumer.h"

namespace CMSat {

/**
@brief Cleans clauses from false literals & removes satisfied clauses
*/
class ClauseCleaner
{
    public:
        ClauseCleaner(Solver& solver);

        enum ClauseSetType {clauses, binaryClauses, xorclauses, learnts};

        void cleanClauses(vec<Clause*>& cs, ClauseSetType type, const uint32_t limit = 0);

        void cleanClauses(vec<XorClause*>& cs, ClauseSetType type, const uint32_t limit = 0);
        void removeSatisfiedBins(const uint32_t limit = 0);
        //void removeSatisfied(vec<Clause*>& cs, ClauseSetType type, const uint32_t limit = 0);
        //void removeSatisfied(vec<XorClause*>& cs, ClauseSetType type, const uint32_t limit = 0);
        void removeAndCleanAll(const bool nolimit = false);
        bool satisfied(const Clause& c) const;
        bool satisfied(const XorClause& c) const;

    private:
        bool satisfied(const Watched& watched, Lit lit);
        bool cleanClause(XorClause& c);
        bool cleanClause(Clause*& c);

        uint32_t lastNumUnitarySat[6]; ///<Last time we cleaned from satisfied clauses, this many unitary clauses were known
        uint32_t lastNumUnitaryClean[6]; ///<Last time we cleaned from satisfied clauses&false literals, this many unitary clauses were known

        Solver& solver;
};

/**
@brief Removes all satisfied clauses, and cleans false literals

There is a heuristic in place not to try to clean all the time. However,
this limit can be overridden with "nolimit"
@p nolimit set this to force cleaning&removing. Useful if a really clean
state is needed, which is important for certain algorithms
*/
inline void ClauseCleaner::removeAndCleanAll(const bool nolimit)
{
    //uint32_t limit = std::min((uint32_t)((double)solver.order_heap.size() * PERCENTAGECLEANCLAUSES), FIXCLEANREPLACE);
    uint32_t limit = (double)solver.order_heap.size() * PERCENTAGECLEANCLAUSES;
    if (nolimit) limit = 0;

    removeSatisfiedBins(limit);
    cleanClauses(solver.clauses, ClauseCleaner::clauses, limit);
    cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses, limit);
    cleanClauses(solver.learnts, ClauseCleaner::learnts, limit);
}

}

#endif //CLAUSECLEANER_H

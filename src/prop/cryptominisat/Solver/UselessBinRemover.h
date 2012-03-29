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

#ifndef USELESSBINREMOVER_H
#define USELESSBINREMOVER_H

#include "Vec.h"
#include "Solver.h"
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

namespace CMSat {

/**
@brief Removes binary clauses that are effectively useless to have

These binary clauses are useless, because for example clauses:
a V b
-b V c

exist, so the binary clause:
a V c

is useless in every possible way. Here, we remove such claues. Unfortunately,
currently we only remove useless non-learnt binary clauses. Learnt useless
binary clauses are not removed.

\todo Extend such that it removes learnt useless binary clauses as well
*/
class UselessBinRemover {
    public:
        UselessBinRemover(Solver& solver);
        bool removeUslessBinFull();

    private:
        bool failed; ///<Has the previous propagation failed? (=conflict)
        uint32_t extraTime; ///<Time that cannot be meausured in bogoprops (~propagation time)

        //Remove useless binaries
        bool fillBinImpliesMinusLast(const Lit origLit, const Lit lit, vec<Lit>& wrong);
        bool removeUselessBinaries(const Lit lit);
        void removeBin(const Lit lit1, const Lit lit2);
        /**
        @brief Don't delete the same binary twice, and don't assume that deleted binaries still exist

        Not deleting the same binary twice is easy to understand. He hard part
        is the second thought. Basically, once we set "a->b" to be deleted, for
        instance, we should not check whether any one-hop neighbours of "a" can
        be reached from "b", since the binary clause leading to "b" has already
        been deleted (and, by the way, checked, since the place where we can
        reach "b" from already checked for all places we can visit from "b")
        */
        vec<char> toDeleteSet;
        vec<Lit> oneHopAway; ///<Lits that are one hop away from selected lit (sometimes called origLit)
        /**
        @brief Binary clauses to be removed are gathered here

        We only gather the second lit, the one we can reach from selected lit
        (calld origLit some places) see fillBinImpliesMinusLast() for details
        */
        vec<Lit> wrong;

        Solver& solver; ///<The solver class e want to remove useless binary clauses from
};

}

#endif //USELESSBINREMOVER_H

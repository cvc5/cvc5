/**************************************************************************
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
*****************************************************************************/

#ifndef CLAUSEVIVIFIER_H
#define CLAUSEVIVIFIER_H

#include "Solver.h"

namespace CMSat {

class ClauseVivifier {
    public:
        ClauseVivifier(Solver& solver);
        bool vivifyClauses();
        bool vivifyClauses2(vec<Clause*>& clauses);

    private:

        /**
        @brief Records data for asymmBranch()

        Clauses are ordered accurding to sze in asymmBranch() and then some are
        checked if we could shorten them. This value records that between calls
        to asymmBranch() where we stopped last time in the list
        */
        uint32_t lastTimeWentUntil;

        /**
        @brief Sort clauses according to size
        */
        struct sortBySize
        {
            bool operator () (const Clause* x, const Clause* y)
            {
              return (x->size() > y->size());
            }
        };

        void makeNonLearntBin(const Lit lit1, const Lit lit2, const bool learnt);

        uint32_t numCalls;
        Solver& solver;
};

}

#endif //CLAUSEVIVIFIER_H

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

#include "Solver.h"

namespace CMSat {

/**
@brief Helper class to completely detaches all(or only non-native) clauses, and then re-attach all

Used in classes that (may) do a lot of clause-changning, in which case
detaching&reattaching of clauses would be neccessary to do
individually, which is \b very slow

A main use-case is the following:
-# detach all clauses
-# play around with all clauses as desired. Cannot call solver.propagate() here
-# attach all clauses again

A somewhat more complicated, but more interesting use-case is the following:
-# detach only non-natively stored clauses from watchlists
-# play around wil all clauses as desired. 2- and 3-long clauses can still
be propagated with solver.propagate() -- this is quite a nice trick, in fact
-# detach all clauses (i.e. also native ones)
-# attach all clauses
*/
class CompleteDetachReatacher
{
    public:
        CompleteDetachReatacher(Solver& solver);
        bool reattachNonBins();
        void detachNonBinsNonTris(const bool removeTri);

    private:
        class ClausesStay {
            public:
                ClausesStay() :
                    learntBins(0)
                    , nonLearntBins(0)
                    , tris(0)
                {}

                ClausesStay& operator+=(const ClausesStay& other) {
                    learntBins += other.learntBins;
                    nonLearntBins += other.nonLearntBins;
                    tris += other.tris;
                    return *this;
                }

                uint32_t learntBins;
                uint32_t nonLearntBins;
                uint32_t tris;
        };
        const ClausesStay clearWatchNotBinNotTri(vec<Watched>& ws, const bool removeTri = false);

        void cleanAndAttachClauses(vec<Clause*>& cs);
        void cleanAndAttachClauses(vec<XorClause*>& cs);
        bool cleanClause(Clause*& ps);
        bool cleanClause(XorClause& ps);

        Solver& solver;
};

}

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

#ifndef ONLYNONLEARNTBINS_H
#define ONLYNONLEARNTBINS_H

#include "Solver.h"

namespace CMSat {

/**
@brief Handles propagation, addition&removal of non-learnt binary clauses

It takes a snapshot of Solver's non-learnt binary clauses, builds its own
watchlists, and does everything itself.*/
class OnlyNonLearntBins
{
    public:
        OnlyNonLearntBins(Solver& solver);

        /**
        @brief For storing a binary clause
        */
        class WatchedBin {
        public:
            WatchedBin(Lit _impliedLit) : impliedLit(_impliedLit) {};
            Lit impliedLit;
        };

        //propagation
        bool propagate();

        //Management of clauses
        bool fill();

        //helper
        inline uint32_t getWatchSize(const Lit lit) const;
        inline const vec<vec<WatchedBin> >& getBinWatches() const;

    private:
        vec<vec<WatchedBin> > binwatches; ///<Internal wathclists for non-learnt binary clauses

        Solver& solver;
};

inline uint32_t OnlyNonLearntBins::getWatchSize(const Lit lit) const
{
    return binwatches[lit.toInt()].size();
}

inline const vec<vec<OnlyNonLearntBins::WatchedBin> >& OnlyNonLearntBins::getBinWatches() const
{
    return binwatches;
}

}

#endif //ONLYNONLEARNTBINS_H

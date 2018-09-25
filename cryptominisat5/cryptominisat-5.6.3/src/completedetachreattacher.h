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

#ifndef __COMPLETE_DETACH_REATTACHER__
#define __COMPLETE_DETACH_REATTACHER__

#include "constants.h"
#include "watched.h"
#include "watcharray.h"

namespace CMSat {

class Solver;
class Clause;

/**
@brief Helper class to completely detaches all(or only non-native) clauses

Used in classes that (may) do a lot of clause-changning, in which case
detaching&reattaching of clauses would be neccessary to do
individually, which is \b very slow

A main use-case is the following:
-# detach all clauses
-# play around with all clauses as desired. Cannot call solver.propagate() here
-# attach again
*/
class CompleteDetachReatacher
{
    public:
        explicit CompleteDetachReatacher(Solver* solver);
        bool reattachLongs(bool removeStatsFrist = false);
        void detach_nonbins_nontris();
        void reattachLongsNoClean();

    private:
        void attachClauses(vector<ClOffset>& cs);
        void cleanAndAttachClauses(
            vector<ClOffset>& cs
            , bool removeStatsFrist
        );
        bool clean_clause(Clause* cl);

        class ClausesStay {
            public:
                ClausesStay() :
                    redBins(0)
                    , irredBins(0)
                {}

                ClausesStay& operator+=(const ClausesStay& other) {
                    redBins += other.redBins;
                    irredBins += other.irredBins;
                    return *this;
                }

                uint64_t redBins;
                uint64_t irredBins;
        };
        ClausesStay clearWatchNotBinNotTri(watch_subarray ws);

        Solver* solver;
};

} //end namespace

#endif //__COMPLETE_DETACH_REATTACHER__

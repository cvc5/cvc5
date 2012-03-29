/***************************************************************************
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
****************************************************************************/

#ifndef FAILEDLITSEARCHER_H
#define FAILEDLITSEARCHER_H

#include <set>
#include <map>
#include <vector>

#include "SolverTypes.h"
#include "Clause.h"
#include "BitArray.h"

namespace CMSat {

using std::set;
using std::map;
using std::vector;

class Solver;

/**
@brief Responsible for doing failed var searching and related algorithms

Performs in seach():
1) Failed lit searching
2) Searching for lits that have been propagated by both "var" and "~var"
3) 2-long Xor clauses that have been found because when propagating "var" and
   "~var", they have been produced by normal xor-clauses shortening to this xor
   clause
4) If var1 propagates var2 and ~var1 propagates ~var2, then var=var2, and this
   is a 2-long XOR clause, this 2-long xor is added
5) Hyper-binary resolution

Perfoms in asymmBranch(): asymmetric branching, heuristically. Best paper
on this is 'Vivifying Propositional Clausal Formulae', though we do it much
more heuristically
*/
class FailedLitSearcher {
    public:
        FailedLitSearcher(Solver& _solver);

        bool search();
        double getTotalTime() const;

    private:
        //Main
        bool tryBoth(const Lit lit1, const Lit lit2);
        bool tryAll(const Lit* begin, const Lit* end);
        void printResults(const double myTime) const;

        Solver& solver; ///<The solver we are updating&working with

        bool failed; ///<For checking that a specific propagation failed (=conflict). It is used in many places

        //bothprop finding
        vector<uint32_t> propagatedBitSet;
        BitArray propagated; ///<These lits have been propagated by propagating the lit picked
        BitArray propValue; ///<The value (0 or 1) of the lits propagated set in "propagated"
        /**
        @brief Lits that have been propagated to the same value both by "var" and "~var"

        value that the literal has been propagated to is available in propValue
        */
        vec<Lit> bothSame;

        //2-long xor-finding
        /**
        @brief used to find 2-long xor by shortening longer xors to this size

        -# We propagate "var" and record all xors that become 2-long
        -# We propagate "~var" and record all xors that become 2-long
        -# if (1) and (2) have something in common, we add it as a variable
        replacement instruction

        We must be able to order these 2-long xors, so that we can search
        for matching couples fast. This class is used for that
        */
        class TwoLongXor
        {
        public:
            bool operator==(const TwoLongXor& other) const
            {
                if (var[0] == other.var[0]
                    && var[1] == other.var[1]
                    && inverted == other.inverted)
                    return true;
                return false;
            }
            bool operator<(const TwoLongXor& other) const
            {
                if (var[0] < other.var[0]) return true;
                if (var[0] > other.var[0]) return false;

                if (var[1] < other.var[1]) return true;
                if (var[1] > other.var[1]) return false;

                if (inverted < other.inverted) return true;
                if (inverted > other.inverted) return false;

                return false;
            }

            Var var[2];
            bool inverted;
        };

        class BinXorToAdd
        {
            public:
                BinXorToAdd(const Lit _lit1, const Lit _lit2, const bool _isEqualFalse) :
                    lit1(_lit1)
                    , lit2(_lit2)
                    , isEqualFalse(_isEqualFalse)
                {}
                Lit lit1;
                Lit lit2;
                bool isEqualFalse;
        };
        TwoLongXor getTwoLongXor(const XorClause& c);
        void addFromSolver(const vec<XorClause*>& cs);
        void removeVarFromXors(const Var var);
        void addVarFromXors(const Var var);

        uint32_t newBinXor;
        vec<uint32_t> xorClauseSizes;
        vector<vector<uint32_t> > occur; ///<Occurence list for XORs. Indexed by variables
        BitArray xorClauseTouched;
        vec<uint32_t> investigateXor;
        std::set<TwoLongXor> twoLongXors;
        bool binXorFind;
        uint32_t lastTrailSize;
        vector<BinXorToAdd> binXorToAdd;

        /**
        @brief Num. 2-long xor-found through Le Berre paper

        In case:
        -# (a->b, ~a->~b) -> a=b
        -#  binary clause (a,c) exists:  (a->g, c->~g) -> a = ~c
        */
        uint32_t bothInvert;

        //finding HyperBins
        struct LitOrder2
        {
            LitOrder2(const vec<BinPropData>& _binPropData) :
            binPropData(_binPropData)
            {}

            bool operator () (const Lit x, const Lit y) const
            {
                return binPropData[x.var()].lev > binPropData[y.var()].lev;
            }

            const vec<BinPropData>& binPropData;
        };
        struct BinAddData
        {
            vector<Lit> lits;
            Lit lit;
        };
        struct BinAddDataSorter
        {
            bool operator() (const BinAddData& a, const BinAddData& b) const
            {
                return (a.lits.size() > b.lits.size());
            }
        };
        //void addMyImpliesSetAsBins(Lit lit, int32_t& difference);

        uint32_t addedBin;
        void hyperBinResolution(const Lit lit);
        BitArray unPropagatedBin;
        BitArray needToVisit;
        vec<Var> propagatedVars;
        void addBin(const Lit lit1, const Lit lit2);
        void fillImplies(const Lit lit);
        vec<Var> myImpliesSet; ///<variables set in myimplies
        uint64_t hyperbinProps; ///<Number of bogoprops done by the hyper-binary resolution function hyperBinResolution()

        //bin-removal within hyper-bin-res
        vec<Lit> uselessBin;
        uint32_t removedUselessLearnt;
        uint32_t removedUselessNonLearnt;
        BitArray dontRemoveAncestor;
        vec<Var> toClearDontRemoveAcestor;
        /**
        @brief Controls hyper-binary resolution's time-usage

        Don't do more than this many propagations within hyperBinResolution()
        */
        uint64_t maxHyperBinProps;

        //Temporaries
        vec<Lit> tmpPs;

        //State for this run
        /**
        @brief Records num. var-replacement istructions between 2-long xor findings through longer xor shortening

        Finding 2-long xor claues by shortening is fine, but sometimes we find
        the same thing, or find something that is trivially a consequence of
        other 2-long xors that we already know. To filter out these bogus
        "findigs" from the statistics reported, we save in this value the
        real var-replacement insturctions before and after the 2-long xor
        finding through longer xor-shortening, and then compare the changes
        made
        */
        uint32_t toReplaceBefore;
        uint32_t origTrailSize; ///<Records num. of 0-depth assignments at the start-up of search()
        uint64_t origProps;     ///<Records num. of bogoprops at the start-up of search()
        uint32_t numFailed;     ///<Records num. of failed literals during search()
        uint32_t goodBothSame;  ///<Records num. of literals that have been propagated to the same value by both "var" and "~var"

        //State between runs
        double totalTime;
        double numPropsMultiplier; ///<If last time we called search() all went fine, then this is incremented, so we do more searching this time
        uint32_t lastTimeFoundTruths; ///<Records how many unit clauses we found last time we called search()
        uint32_t numCalls; ///<Number of times search() has been called
        uint32_t lastTimeStopped;
};

inline double FailedLitSearcher::getTotalTime() const
{
    return totalTime;
}

}

#endif //FAILEDVARSEARCHER_H

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

#ifndef TRANSCACHE_H
#define TRANSCACHE_H

#include <vector>
#include <limits>
#include <algorithm>
#include <vector>
#include "constants.h"
#include "solvertypes.h"

namespace CMSat {

class Solver;

class LitExtra {
public:
    LitExtra() {}

    LitExtra(const Lit l, const bool onlyNLBin)
    {
        x = ((uint32_t)onlyNLBin) | (l.toInt() << 1);
    }

    const Lit getLit() const
    {
        return Lit::toLit(x>>1);
    }

    bool getOnlyIrredBin() const
    {
        return x&1;
    }

    void setOnlyIrredBin()
    {
        x  |= 0x1;
    }

    bool operator<(const LitExtra other) const
    {
        if (getOnlyIrredBin() && !other.getOnlyIrredBin()) return false;
        if (!getOnlyIrredBin() && other.getOnlyIrredBin()) return true;
        return (getLit() < other.getLit());
    }

    bool operator==(const LitExtra other) const
    {
        return x == other.x;
    }

    bool operator!=(const LitExtra other) const
    {
        return x != other.x;
    }
private:
    uint32_t x;

};

class TransCache {
public:
    TransCache()
        //conflictLastUpdated(std::numeric_limits<uint64_t>::max())
    {}

    bool merge(
        const vector<LitExtra>& otherLits
        , const Lit extraLit
        , const bool red
        , const uint32_t leaveOut
        , vector<uint16_t>& seen
    );
    bool merge(
        const vector<Lit>& otherLits //Lits to add
        , const Lit extraLit //Add this, too to the list of lits
        , const bool red //The step was a redundant-dependent step?
        , const uint32_t leaveOut //Leave this literal out
        , vector<uint16_t>& seen
    );
    void makeAllRed();

    void updateVars(
        const std::vector< uint32_t >& outerToInter
        , const size_t newMaxVars
    );

    std::vector<LitExtra> lits;
    //uint64_t conflictLastUpdated;

private:
    bool mergeHelper(
        const Lit extraLit //Add this, too to the list of lits
        , const bool red //The step was a redundant-dependent step?
        , vector<uint16_t>& seen
    );
};

inline std::ostream& operator<<(std::ostream& os, const TransCache& tc)
{
    for (size_t i = 0; i < tc.lits.size(); i++) {
        os << tc.lits[i].getLit()
        << "(" << (tc.lits[i].getOnlyIrredBin() ? "NL" : "L") << ") ";
    }
    return os;
}

class ImplCache  {
public:
    void print_stats(const Solver* solver) const;
    void print_statsSort(const Solver* solver) const;
    size_t mem_used() const;
    void makeAllRed();
    void save_on_var_memorys(uint32_t newNumVars)
    {
        implCache.resize(newNumVars*2);
        implCache.shrink_to_fit();
    }

    std::vector<TransCache> implCache;

    std::vector<TransCache>::iterator begin()
    {
        return implCache.begin();
    }

    std::vector<TransCache>::iterator end()
    {
        return implCache.end();
    }

    std::vector<TransCache>::const_iterator begin() const
    {
        return implCache.begin();
    }

    std::vector<TransCache>::const_iterator end() const
    {
        return implCache.end();
    }

    const TransCache& operator[](const Lit at) const
    {
        return implCache[at.toInt()];
    }

    TransCache& operator[](const Lit at)
    {
        return implCache[at.toInt()];
    }

    void new_var()
    {
        implCache.push_back(TransCache());
        implCache.push_back(TransCache());
    }

    void new_vars(const size_t n)
    {
        implCache.insert(implCache.end(), 2*n, TransCache());
    }

    size_t size() const
    {
        return implCache.size();
    }

    void updateVars(
        vector<uint16_t>& seen
        , const std::vector< uint32_t >& outerToInter
        , const std::vector< uint32_t >& interToOuter2
        , const size_t newMaxVars
    );

    bool clean(Solver* solver, bool* setSomething = NULL);
    bool tryBoth(Solver* solver);

    struct TryBothStats
    {
        void clear()
        {
            TryBothStats tmp;
            *this = tmp;
        }

        TryBothStats& operator+=(const TryBothStats& other);
        void print_short(Solver* solver) const;

        uint64_t numCalls = 0;
        double cpu_time = 0;
        uint64_t zeroDepthAssigns = 0;
        uint64_t varReplaced = 0;
        uint64_t bProp = 0;
        uint64_t bXProp = 0;
    };

    TryBothStats runStats;
    TryBothStats globalStats;
    const TryBothStats& get_stats() const
    {
        return globalStats;
    }

    void free()
    {
        vector<TransCache> tmp;
        implCache.swap(tmp);
    }

    void clear()
    {
        for(vector<TransCache>::iterator
            it = implCache.begin(), end = implCache.end()
            ; it != end
            ; ++it
        ) {
            it->lits.clear();
        }
    }

private:
    void tryVar(Solver* solver, uint32_t var);

    void handleNewData(
        vector<uint8_t>& val
        , uint32_t var
        , Lit lit
    );

    vector< std::pair<std::pair<Lit, Lit>, bool> > delayedClausesToAddXor;
    vector<Lit> delayedClausesToAddNorm;
    bool addDelayedClauses(Solver* solver);
};

} //end namespace

namespace std
{
    template <>
    inline void swap (CMSat::TransCache& m1, CMSat::TransCache& m2)
    #ifdef _MSC_VER
    throw()
    #else
    noexcept (true)
    #endif
    {
         m1.lits.swap(m2.lits);
    }
}

#endif //TRANSCACHE_H

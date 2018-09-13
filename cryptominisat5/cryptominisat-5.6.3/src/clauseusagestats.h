/*************************************************************
MiniSat       --- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat --- Copyright (c) 2014, Mate Soos

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
***************************************************************/

#ifndef __CLAUSEUSAGESTATS_H__
#define __CLAUSEUSAGESTATS_H__

#include <cstdint>
#include "clause.h"

namespace CMSat {

struct ClauseUsageStats
{
    uint64_t sumPropAndConfl() const
    {
        return sumProp + sumConfl;
    }

    uint64_t num = 0;
    uint64_t sumProp = 0;
    uint64_t sumConfl = 0;
    uint64_t sumLookedAt = 0;
    uint64_t sumUsedUIP = 0;

    ClauseUsageStats& operator+=(const ClauseUsageStats& other)
    {
        num += other.num;
        sumProp += other.sumProp;
        sumConfl += other.sumConfl;
        sumLookedAt += other.sumLookedAt;
        sumUsedUIP += other.sumUsedUIP;

        return *this;
    }

    void addStat(const Clause&
    #ifdef STATS_NEEDED
    cl
    #endif
    ) {
        num++;
        #ifdef STATS_NEEDED
        sumConfl += cl.stats.conflicts_made;
        sumProp += cl.stats.propagations_made;
        sumLookedAt += cl.stats.clause_looked_at;
        sumUsedUIP += cl.stats.used_for_uip_creation;
        #endif
    }
    void print() const;
};

}

#endif //__CLAUSEUSAGESTATS_H__

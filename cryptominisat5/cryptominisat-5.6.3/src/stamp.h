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

#ifndef __STAMP_H__
#define __STAMP_H__

#include <vector>
#include <algorithm>
#include "solvertypes.h"
#include "clause.h"
#include "constants.h"

namespace CMSat {

using std::vector;

enum StampType {
    STAMP_IRRED = 0
    , STAMP_RED = 1
};

struct Timestamp
{
    Timestamp()
    {
        start[STAMP_IRRED] = 0;
        start[STAMP_RED] = 0;

        end[STAMP_IRRED] = 0;
        end[STAMP_RED] = 0;
    }

    uint64_t start[2];
    uint64_t end[2];
};

class Stamp
{
public:
    bool stampBasedClRem(const vector<Lit>& lits) const;
    std::pair<size_t, size_t> stampBasedLitRem(
        vector<Lit>& lits
        , StampType stampType
    ) const;
    void updateVars(
        const vector<uint32_t>& outerToInter
        , const vector<uint32_t>& interToOuter2
        , vector<uint16_t>& seen
    );
    void clearStamps();
    void save_on_var_memory(const uint32_t newNumVars);

    uint64_t stampingTime = 0;
    vector<Timestamp>   tstamp;
    void new_var()
    {
        tstamp.push_back(Timestamp());
        tstamp.push_back(Timestamp());
    }
    void new_vars(const size_t n)
    {
        tstamp.insert(tstamp.end(), 2*n, Timestamp());
    }
    size_t mem_used() const
    {
        return tstamp.capacity()*sizeof(Timestamp);
    }

    void freeMem()
    {
        vector<Timestamp> tmp;
        tstamp.swap(tmp);
    }

private:
    struct StampSorter
    {
        StampSorter(
            const vector<Timestamp>& _timestamp
            , const StampType _stampType
            , const bool _rev
        ) :
            timestamp(_timestamp)
            , stampType(_stampType)
            , rev(_rev)
        {}

        const vector<Timestamp>& timestamp;
        const StampType stampType;
        const bool rev;

        bool operator()(const Lit lit1, const Lit lit2) const
        {
            if (!rev) {
                return timestamp[lit1.toInt()].start[stampType]
                        < timestamp[lit2.toInt()].start[stampType];
            } else {
                return timestamp[lit1.toInt()].start[stampType]
                        > timestamp[lit2.toInt()].start[stampType];
            }
        }
    };

    struct StampSorterInv
    {
        StampSorterInv(
            const vector<Timestamp>& _timestamp
            , const StampType _stampType
            , const bool _rev
        ) :
            timestamp(_timestamp)
            , stampType(_stampType)
            , rev(_rev)
        {}

        const vector<Timestamp>& timestamp;
        const StampType stampType;
        const bool rev;

        bool operator()(const Lit lit1, const Lit lit2) const
        {
            if (!rev) {
                return timestamp[(~lit1).toInt()].start[stampType]
                    < timestamp[(~lit2).toInt()].start[stampType];
            } else {
                return timestamp[(~lit1).toInt()].start[stampType]
                    > timestamp[(~lit2).toInt()].start[stampType];
            }
        }
    };

    mutable vector<Lit> stampNorm;
    mutable vector<Lit> stampInv;
};

} //end namespace

#endif //__STAMP_H__

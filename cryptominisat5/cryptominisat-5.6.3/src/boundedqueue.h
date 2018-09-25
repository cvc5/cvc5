/***************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
2008 - Gilles Audemard, Laurent Simon
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

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
****************************************************************************/

#ifndef BOUNDEDQUEUE_H
#define BOUNDEDQUEUE_H

#include "constants.h"
#include "avgcalc.h"
#include <cassert>
#include <vector>
#include <cstring>
#include <sstream>
#include <iomanip>

namespace CMSat {
using std::vector;

template <class T, class T2 = uint64_t>
class bqueue {
    //Only stores info for N elements
    vector<T>  elems;
    uint32_t first;
    uint32_t last;
    uint32_t maxsize; //max number of history elements
    uint32_t queuesize; // Number of current elements (must be < maxsize !)
    T2  sumofqueue;
    #ifdef STATS_NEEDED
    AvgCalc<T, T2> longTermAvg;
    #endif

public:
    bqueue(void) :
        first(0)
        , last(0)
        , maxsize(0)
        , queuesize(0)
        , sumofqueue(0)
    {}

    size_t usedMem() const
    {
        return sizeof(size_t)*4 + elems.capacity()*sizeof(T) + sizeof(T2) + sizeof(AvgCalc<T,T2>);
    }

    void push(const T x) {
        if (queuesize == maxsize) {
            // The queue is full, next value to enter will replace oldest one

            assert(last == first);
            sumofqueue -= elems[last];

            last++;
            if (last == maxsize)
                last = 0;

        } else {
            queuesize++;
        }

        sumofqueue += x;

        #ifdef STATS_NEEDED
        longTermAvg.push(x);
        #endif
        elems[first] = x;

        first++;
        if (first == maxsize)
            first = 0;
    }

    double avg() const
    {
        if (queuesize == 0)
            return 0;

        assert(isvalid());
        return (double)sumofqueue/(double)queuesize;
    }

    double avg_nocheck() const
    {
        if (queuesize == 0)
            return 0;

        return (double)sumofqueue/(double)queuesize;
    }

    #ifdef STATS_NEEDED
    const AvgCalc<T,T2>& getLongtTerm() const
    {
        return longTermAvg;
    }

    T prev(int32_t p) const
    {
        if (p > (int32_t)queuesize)
            return 0;

        uint32_t e;
        if (first > 0) {
            e = first-1;
        } else {
            e = maxsize-1;
        }

        while(p-- > 0) {
            if (e == 0) {
                e = maxsize-1;
            } else {
                e--;
            }
        }
        return elems[e];
    }
    #endif

    std::string getAvgPrint(size_t prec, size_t w) const
    {
        std::stringstream ss;
        if (isvalid()) {
            ss
            << std::fixed << std::setprecision(prec) << std::setw(w) << std::right
            << avg();
        } else {
            ss << std::setw(5) << "?";
        }

        return ss.str();
    }

    bool isvalid() const
    {
        return (queuesize == maxsize);
    }

    void clearAndResize(const size_t size)
    {
        clear();
        elems.resize(size);
        maxsize = size;
    }

    void clear()
    {
        first = 0;
        last = 0;
        queuesize = 0;
        sumofqueue = 0;

        #ifdef STATS_NEEDED
        longTermAvg.clear();
        #endif
    }

    size_t get_size() const
    {
        return queuesize;
    }

    size_t get_maxsize() const
    {
        return maxsize;
    }
};

} //end namespace

#endif //BOUNDEDQUEUE_H

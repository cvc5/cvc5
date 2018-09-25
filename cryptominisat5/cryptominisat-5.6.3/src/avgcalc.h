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

#ifndef __AVGCALC_H__
#define __AVGCALC_H__

#include "constants.h"
#include <limits>
#include <cassert>
#include <vector>
#include <cstring>
#include <sstream>
#include <iomanip>

namespace CMSat {
using std::vector;

#define AVGCALC_NEED_MIN_MAX

template <class T, class T2 = uint64_t>
class AvgCalc {
    T2      sum;
    size_t  num;
    #ifdef STATS_NEEDED
    double  sumSqare;
    #endif
    #ifdef AVGCALC_NEED_MIN_MAX
    T       min;
    T       max;
    #endif

public:
    AvgCalc(void) :
        sum(0)
        , num(0)
        #ifdef STATS_NEEDED
        , sumSqare(0)
        #endif
        #ifdef AVGCALC_NEED_MIN_MAX
        , min(std::numeric_limits<T>::max())
        , max(std::numeric_limits<T>::min())
        #endif
    {}

    AvgCalc<T, T2>& operator/=(const T2 val)
    {
        sum /= val;
        min /= val;
        max /= val;
        #ifdef STATS_NEEDED
        sumSqare /= val*val;
        #endif

        return *this;
    }

    AvgCalc<T, T2>& operator+=(const AvgCalc<T, T2>& other)
    {
        sum += other.sum;
        num += other.num;
        min = std::min(min, other.min);
        max = std::min(min, other.max);
        #ifdef STATS_NEEDED
        sumSqare += other.sumSqare;
        #endif

        return *this;
    }

    AvgCalc<T, T2>& operator-=(const AvgCalc<T, T2>& other)
    {
        sum += other.sum;
        num += other.num;
        min = std::min(min, other.min);
        max = std::min(min, other.max);
        #ifdef STATS_NEEDED
        sumSqare += other.sumSqare;
        #endif

        return *this;
    }

    T2 get_sum() const
    {
        return sum;
    }

    void push(const T x) {
        sum += x;
        num++;

        #ifdef STATS_NEEDED
        sumSqare += (double)x*(double)x;
        #endif
        #ifdef AVGCALC_NEED_MIN_MAX
        max = std::max(max, x);
        min = std::min(min, x);
        #endif
    }

    #ifdef AVGCALC_NEED_MIN_MAX
    T getMin() const
    {
        if (min == std::numeric_limits<T>::max())
            return 0;

        return min;
    }

    T getMax() const
    {
        if (max == std::numeric_limits<T>::min())
            return 0;

        return max;
    }
    #endif
    #ifdef STATS_NEEDED
    double var() const
    {
        if (num == 0)
            return 0;

        const double calcAvg = avg();
        return
            (((double)sumSqare
                - 2.0*calcAvg*(double)sum
            ))/(double)num
             + calcAvg*calcAvg;
    }
    #endif

    double avg() const
    {
        if (num == 0)
            return 0;

        return (double)sum/(double)num;
    }

    std::string avgPrint(size_t prec, size_t w) const
    {
        std::stringstream ss;
        if (num > 0) {
            ss << std::fixed << std::setprecision(prec) << std::setw(w) << std::left
            << avg();
        } else {
            ss << std::setw(w) << "?";
        }

        return ss.str();
    }

    void clear()
    {
        AvgCalc<T, T2> tmp;
        *this = tmp;
    }

    void addData(const AvgCalc& other)
    {
        sum += other.sum;
        num += other.num;

        #ifdef STATS_NEEDED
        sumSqare += other.sumSqare;
        #endif
        #ifdef AVGCALC_NEED_MIN_MAX
        min = std::min(min, other.min);
        max = std::max(max, other.max);
        #endif
    }

    size_t num_data_elements() const
    {
        return num;
    }
};

} //end namespace

#endif //__AVGCALC_H__

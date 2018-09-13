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

#ifndef _SEARCHHIST_H_
#define _SEARCHHIST_H_

#include <cstdint>
#include "avgcalc.h"
#include "boundedqueue.h"
#include <iostream>
using std::cout;
using std::endl;

namespace CMSat {

//History
struct SearchHist {
    //About the search
    AvgCalc<uint32_t>   branchDepthHist;     ///< Avg branch depth in current restart
    AvgCalc<uint32_t>   branchDepthDeltaHist;

    AvgCalc<uint32_t>   backtrackLevelHistLT;
    AvgCalc<uint32_t>   trailDepthHistLT;
    AvgCalc<uint32_t>   vsidsVarsAvgLT; //vsids_vars.avg()

    bqueue<uint32_t>    trailDepthHistLonger; ///<total depth, incl. props, decisions and assumps
    AvgCalc<uint32_t>   trailDepthDeltaHist; ///<for THIS restart only

    //About the confl generated
    bqueue<uint32_t>    glueHist;   ///< Set of last decision levels in (glue of) conflict clauses
    AvgCalc<uint32_t>   glueHistLTLimited; //LIMITED, only glue-based restart, max 50 glue
    AvgCalc<uint32_t>   glueHistLTAll;

    AvgCalc<uint32_t>   conflSizeHist;       ///< Conflict size history
    AvgCalc<uint32_t>   conflSizeHistLT;
    AvgCalc<uint32_t>   numResolutionsHistLT;

    #ifdef STATS_NEEDED
    bqueue<uint32_t>    backtrackLevelHist;
    AvgCalc<uint32_t>   overlapHistLT;
    AvgCalc<uint32_t>   antec_data_sum_sizeHistLT;
    AvgCalc<uint32_t>   numResolutionsHist;  ///< Number of resolutions during conflict analysis of THIS restart
    AvgCalc<uint32_t>   decisionLevelHistLT;
    bqueue<uint32_t>    branchDepthHistQueue;
    bqueue<uint32_t>    trailDepthHist;
    #endif

    size_t mem_used() const
    {
        uint64_t used = sizeof(SearchHist);
        used += sizeof(AvgCalc<uint32_t>)*16;
        used += sizeof(AvgCalc<bool>)*4;
        used += sizeof(AvgCalc<size_t>)*2;
        used += sizeof(AvgCalc<double, double>)*2;
        used += glueHist.usedMem();
        used += trailDepthHistLonger.usedMem();
        #ifdef STATS_NEEDED
        used += backtrackLevelHist.usedMem();
        used += branchDepthHistQueue.usedMem();
        #endif

        return used;
    }

    void clear()
    {
        //About the search
        branchDepthHist.clear();
        branchDepthDeltaHist.clear();
        trailDepthDeltaHist.clear();

        //conflict generated
        glueHist.clear();
        conflSizeHist.clear();

        #ifdef STATS_NEEDED
        numResolutionsHist.clear();
        trailDepthHist.clear();
        branchDepthHistQueue.clear();
        #endif
    }

    void reset_glue_hist_size(size_t shortTermHistorySize)
    {
        glueHist.clearAndResize(shortTermHistorySize);
        #ifdef STATS_NEEDED
        backtrackLevelHist.clearAndResize(shortTermHistorySize);
        trailDepthHist.clearAndResize(shortTermHistorySize);
        branchDepthHistQueue.clearAndResize(shortTermHistorySize);
        #endif
    }

    void setSize(const size_t shortTermHistorySize, const size_t blocking_trail_hist_size)
    {
        glueHist.clearAndResize(shortTermHistorySize);
        trailDepthHistLonger.clearAndResize(blocking_trail_hist_size);
        #ifdef STATS_NEEDED
        backtrackLevelHist.clearAndResize(shortTermHistorySize);
        trailDepthHist.clearAndResize(shortTermHistorySize);
        branchDepthHistQueue.clearAndResize(shortTermHistorySize);
        #endif
    }

    void print() const
    {
        cout
        << " glue"
        << " "
        #ifdef STATS_NEEDED
        << std::right << glueHist.getLongtTerm().avgPrint(1, 5)
        #endif
        << "/" << std::left << glueHistLTAll.avgPrint(1, 5)

        << " confllen"
        << " " << std::right << conflSizeHist.avgPrint(1, 5)
        << "/" << std::left << conflSizeHistLT.avgPrint(1, 5)

        << " branchd"
        << " " << std::right << branchDepthHist.avgPrint(1, 5)
        << " branchdd"

        << " " << std::right << branchDepthDeltaHist.avgPrint(1, 4)

        #ifdef STATS_NEEDED
        << " traild"
        << " " << std::right << trailDepthHist.getLongtTerm().avgPrint(0, 7)
        #endif

        << " traildd"
        << " " << std::right << trailDepthDeltaHist.avgPrint(0, 5)
        ;

        cout << std::right;
    }
};

} //end namespace

#endif //_SEARCHHIST_H_

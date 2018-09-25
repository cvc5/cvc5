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

#ifndef _TOPLEVELGAUSS_H_
#define _TOPLEVELGAUSS_H_

#include "xor.h"
#include "toplevelgaussabst.h"
#include <vector>
#include <set>
using std::vector;
using std::set;

namespace CMSat {

class Solver;

class TopLevelGauss: public TopLevelGaussAbst
{
public:
    explicit TopLevelGauss(Solver* _solver);
    bool toplevelgauss(const vector<Xor>& _xors, vector<Lit>* _out_changed_occur) override;

    struct Stats
    {
        void clear()
        {
            Stats tmp;
            *this = tmp;
        }

        double total_time() const
        {
            return extractTime + blockCutTime;
        }

        Stats& operator+=(const Stats& other);
        void print_short(const Solver* solver) const;
        void print() const;

        //Time
        uint32_t numCalls = 0;
        double extractTime = 0.0;
        double blockCutTime = 0.0;

        //XOR stats
        uint64_t numVarsInBlocks = 0;
        uint64_t numBlocks = 0;

        //Usefulness stats
        uint64_t time_outs = 0;
        uint64_t newUnits = 0;
        uint64_t newBins = 0;

        size_t zeroDepthAssigns = 0;
    };

    Stats runStats;
    Stats globalStats;
    size_t mem_used() const override;

private:
    Solver* solver;
    vector<Lit>* out_changed_occur; // may have changed the occur count of these literals

    bool extractInfo();
    void cutIntoBlocks(const vector<size_t>& xorsToUse);
    bool extractInfoFromBlock(const vector<uint32_t>& block, const size_t blockNum);
    void move_xors_into_blocks();

    //Major calculated data and indexes to this data
    vector<vector<uint32_t> > blocks; ///<Blocks of vars that are in groups of XORs
    vector<uint32_t> varToBlock; ///<variable-> block index map

    //Temporaries for putting xors into matrix, and extracting info from matrix
    vector<uint32_t> outerToInterVarMap;
    vector<uint32_t> interToOUterVarMap;

    vector<Xor> xors;
    vector<vector<uint32_t> > xors_in_blocks;
};

}

#endif // _TOPLEVELGAUSS_H_

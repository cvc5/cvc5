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

#include "toplevelgauss.h"
#include "time_mem.h"
#include "solver.h"
#include "occsimplifier.h"
#include "clauseallocator.h"
#include <m4ri/m4ri.h>
#include <limits>
#include <cstddef>
#include "sqlstats.h"

using namespace CMSat;
using std::cout;
using std::endl;

TopLevelGauss::TopLevelGauss(Solver* _solver) :
    solver(_solver)
{
    //NOT THREAD SAFE BUG
    m4ri_build_all_codes();
}

bool TopLevelGauss::toplevelgauss(const vector<Xor>& _xors, vector<Lit>* _out_changed_occur)
{
    out_changed_occur = _out_changed_occur;
    runStats.clear();
    runStats.numCalls = 1;
    xors = _xors;

    size_t origTrailSize = solver->trail_size();
    extractInfo();

    if (solver->conf.verbosity) {
        runStats.print_short(solver);
    }
    runStats.zeroDepthAssigns = solver->trail_size() - origTrailSize;
    if (solver->sqlStats) {
        solver->sqlStats->time_passed_min(
            solver
            , "toplevelgauss"
            , runStats.total_time()
        );
    }
    globalStats += runStats;

    return solver->okay();
}

struct XorSorter{
    bool operator()(const Xor& a, const Xor& b) const
    {
        return a.size() > b.size();
    }
};

bool TopLevelGauss::extractInfo()
{
    double myTime = cpuTime();

    //Order XORs so that larger are first. this way, putting them into blocks
    //will be faster
    std::sort(xors.begin(), xors.end(), XorSorter());

    //Pre-filter XORs -- don't use any XOR which is not connected to ANY
    //other XOR. These cannot be XOR-ed with anything anyway
    vector<uint32_t> varsIn(solver->nVars(), 0);
    for(const Xor& x: xors) {
        for(const uint32_t v: x) {
            varsIn[v]++;
        }
    }

    size_t i = 0;
    vector<size_t> xorsToUse;
    for(vector<Xor>::const_iterator
        it = xors.begin(), end = xors.end()
        ; it != end
        ; ++it, i++
    ) {
        const Xor& thisXor = *it;
        bool makeItIn = false;
        for(uint32_t v: thisXor) {
            if (varsIn[v] > 1) {
                makeItIn = true;
                break;
            }
        }
        //If this clause is not connected to ANY other, skip
        if (!makeItIn)
            continue;

        xorsToUse.push_back(i);
    }

    //Cut above-filtered XORs into blocks
    cutIntoBlocks(xorsToUse);
    move_xors_into_blocks();
    runStats.blockCutTime += cpuTime() -myTime;
    myTime = cpuTime();

    //These mappings will be needed for the matrixes, which will have far less
    //variables than solver->nVars()
    outerToInterVarMap.clear();
    outerToInterVarMap.resize(solver->nVars(), std::numeric_limits<uint32_t>::max());
    interToOUterVarMap.clear();
    interToOUterVarMap.resize(solver->nVars(), std::numeric_limits<uint32_t>::max());

    //Go through all blocks, and extract info
    i = 0;
    for(vector<vector<uint32_t> >::const_iterator
        it = blocks.begin(), end = blocks.end()
        ; it != end
        ; ++it, i++
    ) {
        //If block is already merged, skip
        if (it->empty())
            continue;

        double t = cpuTime();
        const uint64_t oldNewUnits = runStats.newUnits;
        const uint64_t oldNewBins = runStats.newBins;

        if (!extractInfoFromBlock(*it, i))
            goto end;

        if (solver->conf.verbosity >= 5) {
            cout << "Block size: " << it->size() << endl;
            cout << "New units this round: " << (runStats.newUnits - oldNewUnits) << endl;
            cout << "New bins this round: " << (runStats.newBins - oldNewBins) << endl;
            cout << "Time: " << std::setprecision(3) << std::fixed << (cpuTime() - t) << endl;
        }
    }

end:
    runStats.extractTime += cpuTime() - myTime;

    return solver->okay();
}

bool TopLevelGauss::extractInfoFromBlock(
    const vector<uint32_t>& block
    , const size_t blockNum
) {
    assert(solver->okay());
    if (block.empty()) {
        return solver->okay();
    }

    //Outer-inner var mapping is needed because not all vars are in the matrix
    size_t num = 0;
    for(vector<uint32_t>::const_iterator
        it2 = block.begin(), end2 = block.end()
        ; it2 != end2
        ; it2++, num++
    ) {
        //Used to put XOR into matrix
        outerToInterVarMap[*it2] = num;

        //Used to transform new data in matrix to solver
        interToOUterVarMap[num] = *it2;
    }

    //Get corresponding XORs
    const vector<uint32_t>& thisXors = xors_in_blocks[blockNum];
    assert(thisXors.size() > 1 && "We pre-filter the set such that *every* block contains at least 2 xors");

    //Set up matrix
    uint64_t numCols = block.size()+1; //we need augmented column
    uint64_t matSize = numCols*thisXors.size();
    matSize /= 1000ULL*1000ULL;
    if (matSize > solver->conf.maxXORMatrix) {
        //this matrix is way too large, skip :(
        if (solver->conf.verbosity) {
            cout << "c skipping matrix " << thisXors.size() << " x " << numCols << " size:" << matSize << endl;
        }
        return solver->okay();
    }
    mzd_t *mat = mzd_init(thisXors.size(), numCols);
    assert(mzd_is_zero(mat));

    //Fill row-by-row
    size_t row = 0;
    for(vector<uint32_t>::const_iterator
        it = thisXors.begin(), end2 = thisXors.end()
        ; it != end2
        ; ++it, row++
    ) {
        const Xor& thisXor = xors[*it];
        assert(thisXor.size() > 2 && "All XORs must be larger than 2-long");
        //Put XOR into the matrix
        for(uint32_t v: thisXor) {
            const uint32_t var = outerToInterVarMap[v];
            assert(var < numCols-1);
            mzd_write_bit(mat, row, var, 1);
        }

        //Add RHS to the augmented columns
        if (thisXor.rhs)
            mzd_write_bit(mat, row, numCols-1, 1);
    }

    //Fully echelonize
    mzd_echelonize_pluq(mat, true);

    //Examine every row if it gives some new short truth
    vector<Lit> lits;
    for(size_t i = 0; i < row; i++) {
        //Extract places where it's '1'
        lits.clear();
        for(size_t c = 0; c < numCols-1; c++) {
            if (mzd_read_bit(mat, i, c))
                lits.push_back(Lit(interToOUterVarMap[c], false));

            //No point in going on, we cannot do anything with >2-long XORs
            if (lits.size() > 2)
                break;
        }

        //Extract RHS
        const bool rhs = mzd_read_bit(mat, i, numCols-1);

        switch(lits.size()) {
            case 0:
                //0-long XOR clause is equal to 1? If so, it's UNSAT
                if (rhs) {
                    solver->add_xor_clause_inter(lits, 1, false);
                    assert(!solver->okay());
                    goto end;
                }
                break;

            case 1: {
                runStats.newUnits++;
                solver->add_xor_clause_inter(lits, rhs, false);
                if (!solver->okay())
                    goto end;
                break;
            }

            case 2: {
                runStats.newBins++;
                out_changed_occur->insert(out_changed_occur->end(), lits.begin(), lits.end());
                solver->add_xor_clause_inter(lits, rhs, false);
                if (!solver->okay())
                    goto end;
                break;
            }

            default:
                //if resulting xor is larger than 2-long, we cannot extract anything.
                break;
        }
    }

    //Free mat, and return what need to be returned
    end:
    mzd_free(mat);

    return solver->okay();
}

void TopLevelGauss::move_xors_into_blocks()
{
    xors_in_blocks.clear();
    xors_in_blocks.resize(blocks.size());

    for(size_t i = 0; i < xors.size(); i++) {
        const Xor& thisXor = xors[i];
        assert(thisXor.size() > 2 && "XORs are always at least 3-long!");

        uint32_t block = varToBlock[thisXor[0]];
        if (block != std::numeric_limits<uint32_t>::max()) {
            assert(block < xors_in_blocks.size());
            xors_in_blocks[block].push_back(i);
        }
    }
}

void TopLevelGauss::cutIntoBlocks(const vector<size_t>& xorsToUse)
{
    //Clearing data we will fill below
    varToBlock.clear();
    varToBlock.resize(solver->nVars(), std::numeric_limits<uint32_t>::max());
    blocks.clear();

    //Go through each XOR, and either make a new block for it
    //or merge it into an existing block
    //or merge it into an existing block AND merge blocks it joins together
    for(size_t i: xorsToUse) {
        const Xor& thisXor = xors[i];

        //Calc blocks for this XOR
        set<size_t> blocksBelongTo;
        for(uint32_t v: thisXor) {
            assert(solver->varData[v].removed == Removed::none);
            if (varToBlock[v] != std::numeric_limits<uint32_t>::max())
                blocksBelongTo.insert(varToBlock[v]);
        }

        switch(blocksBelongTo.size()) {
            case 0: {
                //Create new block
                vector<uint32_t> block;
                for(uint32_t v: thisXor) {
                    varToBlock[v] = blocks.size();
                    block.push_back(v);
                }
                blocks.push_back(block);
                runStats.numBlocks++;

                continue;
            }

            case 1: {
                //Add to existing block
                const size_t blockNum = *blocksBelongTo.begin();
                vector<uint32_t>& block = blocks[blockNum];
                for(uint32_t v :thisXor) {
                    if (varToBlock[v] == std::numeric_limits<uint32_t>::max()) {
                        block.push_back(v);
                        varToBlock[v] = blockNum;
                    }
                }
                continue;
            }

            default: {
                //Merge blocks into first block
                const size_t blockNum = *blocksBelongTo.begin();
                set<size_t>::const_iterator it2 = blocksBelongTo.begin();
                vector<uint32_t>& finalBlock = blocks[blockNum];
                it2++; //don't merge the first into the first
                for(set<size_t>::const_iterator end2 = blocksBelongTo.end(); it2 != end2; it2++) {
                    for(vector<uint32_t>::const_iterator
                        it3 = blocks[*it2].begin(), end3 = blocks[*it2].end()
                        ; it3 != end3
                        ; it3++
                    ) {
                        finalBlock.push_back(*it3);
                        varToBlock[*it3] = blockNum;
                    }
                    blocks[*it2].clear();
                    runStats.numBlocks--;
                }

                //add remaining vars
                for(uint32_t v: thisXor) {
                    if (varToBlock[v] == std::numeric_limits<uint32_t>::max()) {
                        finalBlock.push_back(v);
                        varToBlock[v] = blockNum;
                    }
                }
            }
        }
    }

    //caclulate stats
    vector<uint32_t> new_block_num;
    uint32_t i = 0;
    for(vector<vector<uint32_t> >::const_iterator
        it = blocks.begin(), end = blocks.end()
        ; it != end
        ; ++it, i++
    ) {
        //this set has been merged into another set. Skip
        if (it->empty())
            continue;

        //cout << "Block vars: " << it->size() << endl;
        runStats.numVarsInBlocks += it->size();
    }

    if (solver->conf.verbosity) {
        cout << "c [xor-m4ri] Sum vars in blocks: " << runStats.numVarsInBlocks << endl;
    }
}

size_t TopLevelGauss::mem_used() const
{
    size_t mem = 0;
    mem += xors.capacity()*sizeof(Xor);
    mem += blocks.capacity()*sizeof(vector<uint32_t>);
    for(size_t i = 0; i< blocks.size(); i++) {
        mem += blocks[i].capacity()*sizeof(uint32_t);
    }
    mem += varToBlock.capacity()*sizeof(size_t);

    //Temporaries for putting xors into matrix, and extracting info from matrix
    mem += outerToInterVarMap.capacity()*sizeof(size_t);
    mem += interToOUterVarMap.capacity()*sizeof(size_t);

    return mem;
}

void TopLevelGauss::Stats::print_short(const Solver* solver) const
{
    cout
    << "c [xor-m4ri] cut into " << numBlocks << " blcks. "
    << " Vars in blcks: " << numVarsInBlocks
    << solver->conf.print_times(blockCutTime)
    << endl;

    cout
    << "c [xor-m4ri] extr info. "
    << " unit: " << newUnits
    << " bin: " << newBins
    << " 0-depth-ass: " << zeroDepthAssigns
    << solver->conf.print_times(extractTime)
    << endl;
}

void TopLevelGauss::Stats::print() const
{
    cout << "c --------- XOR STATS ----------" << endl;

    print_stats_line("c XOR Num calls"
        , numCalls
    );

    print_stats_line("c XOR 0-depth assings"
        , zeroDepthAssigns
    );

    print_stats_line("c XOR unit found"
        , newUnits
    );

    print_stats_line("c XOR bin found"
        , newBins
    );

    cout << "c --------- XOR STATS END ----------" << endl;
}

TopLevelGauss::Stats& TopLevelGauss::Stats::operator+=(const TopLevelGauss::Stats& other)
{
    numCalls += other.numCalls;
    extractTime += other.numCalls;
    blockCutTime += other.numCalls;

    numVarsInBlocks += other.numCalls;
    numBlocks += other.numCalls;

    time_outs += other.numCalls;
    newUnits += other.numCalls;
    newBins += other.numCalls;

    zeroDepthAssigns += other.zeroDepthAssigns;
    return *this;
}

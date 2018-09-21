/******************************************
Copyright (c) 2018  Mate Soos
Copyright (c) 2012  Cheng-Shen Han
Copyright (c) 2012  Jie-Hong Roland Jiang

For more information, see " When Boolean Satisfiability Meets Gaussian
Elimination in a Simplex Way." by Cheng-Shen Han and Jie-Hong Roland Jiang
in CAV (Computer Aided Verification), 2012: 410-426


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

#ifndef PACKEDMATRIX_H
#define PACKEDMATRIX_H

#include <algorithm>
#include <cstdint>
#include "packedrow.h"

//#define DEBUG_MATRIX

namespace CMSat {

class PackedMatrix
{
public:
    PackedMatrix() :
        mp(NULL)
        , numRows(0)
        , numCols(0)
    {
    }

    ~PackedMatrix()
    {
        delete[] mp;
    }

    void resize(const uint32_t num_rows, uint32_t num_cols)
    {
        num_cols = num_cols / 64 + (bool)(num_cols % 64);
        if (numRows*(numCols+1) < num_rows*(num_cols+1)) {
            delete[] mp;
            mp = new uint64_t[num_rows*(num_cols+1)];
        }

        numRows = num_rows;
        numCols = num_cols;
    }

    void resizeNumRows(const uint32_t num_rows)
    {
        #ifdef DEBUG_MATRIX
        assert(num_rows <= numRows);
        #endif

        numRows = num_rows;
    }

    PackedMatrix& operator=(const PackedMatrix& b)
    {
        #ifdef DEBUG_MATRIX
        //assert(b.numRows > 0 && b.numCols > 0);
        #endif

        if (numRows*(numCols+1) < b.numRows*(b.numCols+1)) {
            delete[] mp;
            mp = new uint64_t[b.numRows*(b.numCols+1)];
        }
        numRows = b.numRows;
        numCols = b.numCols;
        memcpy(mp, b.mp, sizeof(uint64_t)*numRows*(numCols+1));

        return *this;
    }

    inline PackedRow getMatrixAt(const uint32_t i)
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif

        return PackedRow(numCols, mp+i*(numCols+1));

    }

    inline PackedRow getMatrixAt(const uint32_t i) const
    {
        #ifdef DEBUG_MATRIX
        assert(i <= numRows);
        #endif

        return PackedRow(numCols, mp+i*(numCols+1));
    }

    class iterator
    {
    public:
        friend class PackedMatrix;

        PackedRow operator*()
        {
            return PackedRow(numCols, mp);
        }

        iterator& operator++()
        {
            mp += (numCols+1);
            return *this;
        }

        iterator operator+(const uint32_t num) const
        {
            iterator ret(*this);
            ret.mp += (numCols+1)*num;
            return ret;
        }

        uint32_t operator-(const iterator& b) const
        {
            return (mp - b.mp)/((numCols+1));
        }

        void operator+=(const uint32_t num)
        {
            mp += (numCols+1)*num;  // add by f4
        }

        bool operator!=(const iterator& it) const
        {
            return mp != it.mp;
        }

        bool operator==(const iterator& it) const
        {
            return mp == it.mp;
        }

    private:
        iterator(uint64_t* _mp, const uint32_t _numCols) :
            mp(_mp)
            , numCols(_numCols)
        {}

        uint64_t* mp;
        const uint32_t numCols;
    };

    inline iterator beginMatrix()
    {
        return iterator(mp, numCols);
    }

    inline iterator endMatrix()
    {
        return iterator(mp+numRows*(numCols+1), numCols);
    }

    inline uint32_t getSize() const
    {
        return numRows;
    }

private:

    uint64_t* mp;
    uint32_t numRows;
    uint32_t numCols;
};

}

#endif //PACKEDMATRIX_H

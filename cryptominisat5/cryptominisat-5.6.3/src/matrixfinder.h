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

#ifndef MATRIXFINDER_H
#define MATRIXFINDER_H

#include <vector>
#include <map>
#include "xor.h"
#include "constants.h"

namespace CMSat {

class Solver;

using std::map;
using std::vector;
using std::pair;

class MatrixFinder {

    public:
        MatrixFinder(Solver* solver);

        //NOTE "simplify_xors" should always be true except during testing
        bool findMatrixes(bool simplify_xors = true);

    private:
        uint32_t setMatrixes();
        struct MatrixShape
        {
            MatrixShape(uint32_t matrix_num) :
                num(matrix_num)
            {}

            MatrixShape()
            {}

            uint32_t num;
            uint32_t rows = 0;
            uint32_t cols = 0;
            uint32_t sum_xor_sizes = 0;
            double density = 0;

            uint64_t tot_size() const
            {
                return rows*cols;
            }
        };

        struct mysorter
        {
            bool operator () (const MatrixShape& left, const MatrixShape& right)
            {
                return left.sum_xor_sizes < right.sum_xor_sizes;
            }
        };

        inline uint32_t fingerprint(const Xor& c) const;
        inline bool firstPartOfSecond(const Xor& c1, const Xor& c2) const;
        inline bool belong_same_matrix(const Xor& x);

        map<uint32_t, vector<uint32_t> > reverseTable; //matrix -> vars
        vector<uint32_t> table; //var -> matrix
        uint32_t matrix_no;
        vector<Xor> xors;

        Solver* solver;
};

}

#endif //MATRIXFINDER_H

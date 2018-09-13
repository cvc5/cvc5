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

#ifndef GQUEUEDATA_H__
#define GQUEUEDATA_H__

namespace CMSat {

struct GaussQData {
    bool do_eliminate; // we do elimination when basic variable is invoked
    uint32_t e_var;                     // do elimination variable
    uint32_t e_row_n ;         // do elimination row
    PropBy confl;              // for choosing better conflict
    uint32_t conflict_size_gauss; // for choosing better conflict
    int ret_gauss;         // gauss matrix result
    bool xorEqualFalse_gauss;            // conflict xor clause xorEqualFalse
    vector<Lit> conflict_clause_gauss; // for gaussian elimination better conflict


    uint32_t big_gaussnum;   // total gauss time for DPLL
    uint32_t big_propagate;  // total gauss propogation time for DPLL
    uint32_t big_conflict;   // total gauss conflict    time for DPLL
    bool engaus_disable;     // decide to do gaussian elimination
    bool enter_matrix;

    void reset()
    {
        enter_matrix = false;
        do_eliminate = false;
        conflict_clause_gauss.clear();
        xorEqualFalse_gauss = false;
        ret_gauss = 4;
        conflict_size_gauss = std::numeric_limits<uint32_t>::max();
    }

    void reset_stats()
    {
        big_gaussnum = 0;   // total gauss time for DPLL
        big_propagate = 0;  // total gauss propogation time for DPLL
        big_conflict = 0;   // total gauss conflict    time for DPLL
        engaus_disable = 0;     // decide to do gaussian elimination
    }

};

}

#endif

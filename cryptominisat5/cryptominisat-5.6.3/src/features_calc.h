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

#ifndef __FEATURES_FAST_H__
#define __FEATURES_FAST_H__

#include <vector>
#include <limits>
#include <utility>
#include "solvefeatures.h"
#include "cloffset.h"
#include "watched.h"
using std::vector;
using std::pair;
using std::make_pair;

namespace CMSat {

class Solver;

struct SolveFeaturesCalc {
public:
    SolveFeaturesCalc(const Solver* _solver) :
        solver(_solver) {
    }
    SolveFeatures extract();

private:
    void fill_vars_cls();
    void calculate_clause_stats();
    void calculate_variable_stats();
    void calculate_extra_var_stats();
    void calculate_extra_clause_stats();
    void normalise_values();
    void calculate_cl_distributions(
        const vector<ClOffset>& clauses
        , struct SolveFeatures::Distrib& distrib_data
    );


    const Solver* solver;
    template<class Function, class Function2>
    void for_one_clause(
        const Watched& cl
        , const Lit lit
        ,  Function func
        ,  Function2 func_each_lit
    ) const;
    template<class Function, class Function2>
    void for_all_clauses(Function for_each_clause,  Function2 func_each_lit) const;
    struct VARIABLE {
        int numPos = 0;
        int size = 0;
        int horn = 0;
    };

    vector<VARIABLE> myVars;
    SolveFeatures feat;
};

} //end namespace

#endif //__FEATURES_FAST_H__

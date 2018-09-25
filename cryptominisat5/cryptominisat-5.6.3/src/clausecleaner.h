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

#ifndef CLAUSECLEANER_H
#define CLAUSECLEANER_H

#include "constants.h"
#include "watched.h"
#include "watcharray.h"
#include "clause.h"
#include "xor.h"
#include <vector>
using std::vector;

namespace CMSat {

class Solver;

/**
@brief Cleans clauses from false literals & removes satisfied clauses
*/
class ClauseCleaner
{
    public:
        ClauseCleaner(Solver* solver);

        void clean_implicit_clauses();
        void remove_and_clean_all();
        bool satisfied(const Clause& c) const;
        bool clean_xor_clauses(vector<Xor>& xors);

    private:
        bool clean_one_xor(Xor& x);

        //Implicit cleaning
        struct ImplicitData
        {
            uint64_t remNonLBin = 0;
            uint64_t remLBin = 0;

            //We can only attach these in delayed mode, otherwise we would
            //need to manipulate the watchlist we are going through
            vector<BinaryClause> toAttach;

            void update_solver_stats(Solver* solver);
        };
        ImplicitData impl_data;
        void clean_implicit_watchlist(
            watch_subarray& watch_list
            , const Lit lit
        );
        void clean_binary_implicit(
           Watched& ws
            , Watched*& j
            , const Lit lit
        );

        void clean_clauses_pre();
        void clean_clauses_post();
        void clean_clauses_inter(vector<ClOffset>& cs);

        bool satisfied(const Watched& watched, Lit lit);
        bool clean_clause(Clause& c);
        vector<ClOffset> delayed_free;

        Solver* solver;
};

} //end namespace

#endif //CLAUSECLEANER_H

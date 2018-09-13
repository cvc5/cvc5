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

#ifndef PARTFINDER_H
#define PARTFINDER_H

#include <vector>
#include <map>
#include "constants.h"
#include "solvertypes.h"
#include "cloffset.h"

namespace CMSat {

class Solver;
class Clause;

using std::map;
using std::vector;
using std::pair;

class CompFinder {

    public:
        explicit CompFinder(Solver* solver);
        void find_components();
        bool getTimedOut() const;

        const map<uint32_t, vector<uint32_t> >& getReverseTable() const; // comp->var
        uint32_t getVarComp(const uint32_t var) const;
        const vector<uint32_t>& getTable() const; //var -> comp
        const vector<uint32_t>& getCompVars(const uint32_t comp);
        uint32_t getNumComps() const;

    private:
        void addToCompImplicits();
        void add_clauses_to_component(const vector<ClOffset>& cs);
        template<class T>
        void add_clause_to_component(const T& cl);
        template<class T>
        bool belong_to_same_component(const T& cl);
        template<class T>
        void fill_newset_and_tomerge(const T& cl);
        void merge_newset_into_single_component();

        void print_found_components() const;
        bool reverse_table_is_correct() const;
        void print_and_add_to_sql_result(const double myTime) const;

        struct MySorter
        {
            bool operator () (
                const pair<uint32_t, uint32_t>& left
                , const pair<uint32_t, uint32_t>& right
            ) {
                return left.second < right.second;
            }
        };

        //comp -> vars
        map<uint32_t, vector<uint32_t> > reverseTable;

        //var -> comp
        vector<uint32_t> table;

        //The comp counter
        uint32_t comp_no;
        uint32_t used_comp_no;

        //Temporary
        vector<uint32_t> newSet;
        vector<uint32_t> tomerge;

        //Keep track of time
        long long bogoprops_remain;
        long long orig_bogoprops;
        bool timedout;

        vector<uint16_t>& seen;
        Solver* solver;
};

inline uint32_t CompFinder::getNumComps() const
{
    return reverseTable.size();
}

inline const map<uint32_t, vector<uint32_t> >& CompFinder::getReverseTable() const
{
    assert(!timedout);
    return reverseTable;
}

inline const vector<uint32_t>& CompFinder::getTable() const
{
    assert(!timedout);
    return table;
}

inline uint32_t CompFinder::getVarComp(const uint32_t var) const
{
    assert(!timedout);
    return table[var];
}

inline const vector<uint32_t>& CompFinder::getCompVars(const uint32_t comp)
{
    assert(!timedout);
    return reverseTable[comp];
}

inline bool CompFinder::getTimedOut() const
{
    return timedout;
}

} //End namespace

#endif //PARTFINDER_H

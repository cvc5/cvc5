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

#ifndef SCCFINDER_H
#define SCCFINDER_H

#include "clause.h"
#include <stack>
#include <set>

namespace CMSat {

class Solver;

class SCCFinder {
    public:
        explicit SCCFinder(Solver* _solver);
        bool performSCC(uint64_t* bogoprops_given = NULL);
        const std::set<BinaryXor>& get_binxors() const;
        size_t get_num_binxors_found() const;
        void clear_binxors();

        struct Stats
        {
            void clear()
            {
                Stats _tmp;
                *this = _tmp;
            }

            uint64_t numCalls = 0;
            double cpu_time = 0.0;
            uint64_t foundXors = 0;
            uint64_t foundXorsNew = 0;
            uint64_t bogoprops = 0;

            Stats& operator+=(const Stats& other)
            {
                numCalls += other.numCalls;
                cpu_time += other.cpu_time;
                foundXors += other.foundXors;
                foundXorsNew += other.foundXorsNew;
                bogoprops += other.bogoprops;

                return *this;
            }

            void print() const
            {
                cout << "c ----- SCC STATS --------" << endl;
                print_stats_line("c time"
                    , cpu_time
                    , float_div(cpu_time, numCalls)
                    , "per call"
                );

                print_stats_line("c called"
                    , numCalls
                    , float_div(foundXorsNew, numCalls)
                    , "new found per call"
                );

                print_stats_line("c found"
                    , foundXorsNew
                    , stats_line_percent(foundXorsNew, foundXors)
                    , "% of all found"
                );

                print_stats_line("c bogoprops"
                    , bogoprops
                    , "% of all found"
                );

                cout << "c ----- SCC STATS END --------" << endl;
            }

            void print_short(Solver* solver) const;
        };

        const Stats& get_stats() const;
        size_t mem_used() const;
        bool depth_warning_triggered() const;

    private:
        void tarjan(const uint32_t vertex);
        bool depth_warning_issued;
        void doit(const Lit lit, const uint32_t vertex);
        void add_bin_xor_in_tmp();

        //temporaries
        uint32_t globalIndex;
        vector<uint32_t> index;
        vector<uint32_t> lowlink;
        std::stack<uint32_t, vector<uint32_t> > stack;
        vector<char> stackIndicator;
        vector<uint32_t> tmp;
        uint32_t depth;

        Solver* solver;
        std::set<BinaryXor> binxors;

        //Stats
        Stats runStats;
        Stats globalStats;
};

inline void SCCFinder::doit(const Lit lit, const uint32_t vertex) {
    // Was successor v' visited?
    if (index[lit.toInt()] ==  std::numeric_limits<uint32_t>::max()) {
        tarjan(lit.toInt());
        depth--;
        lowlink[vertex] = std::min(lowlink[vertex], lowlink[lit.toInt()]);
    } else if (stackIndicator[lit.toInt()])  {
        lowlink[vertex] = std::min(lowlink[vertex], lowlink[lit.toInt()]);
    }
}

inline bool SCCFinder::depth_warning_triggered() const
{
    return depth_warning_issued;
}

inline const SCCFinder::Stats& SCCFinder::get_stats() const
{
    return globalStats;
}

inline const std::set<BinaryXor>& SCCFinder::get_binxors() const
{
    return binxors;
}

inline size_t SCCFinder::get_num_binxors_found() const
{
    return binxors.size();
}

inline void SCCFinder::clear_binxors()
{
    binxors.clear();
}

} //end namespaceC

#endif //SCCFINDER_H

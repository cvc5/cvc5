/*****************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
******************************************************************************/

#ifndef SCCFINDER_H
#define SCCFINDER_H

#include "Vec.h"
#include "Clause.h"
#include "Solver.h"
#include <stack>

namespace CMSat {

class SCCFinder {
    public:
        SCCFinder(Solver& solver);
        bool find2LongXors();
        double getTotalTime() const;

    private:
        void tarjan(const uint32_t vertex);
        void doit(const Lit lit, const uint32_t vertex);

        uint32_t globalIndex;
        vector<uint32_t> index;
        vector<uint32_t> lowlink;
        std::stack<uint32_t> stack;
        vec<char> stackIndicator;
        vec<uint32_t> tmp;

        uint32_t recurDepth;

        Solver& solver;
        const vec<char>& varElimed1;
        const vec<char>& varElimed2;
        const vector<Lit>& replaceTable;
        double totalTime;
};

inline void SCCFinder::doit(const Lit lit, const uint32_t vertex) {
    // Was successor v' visited?
    if (index[lit.toInt()] ==  std::numeric_limits<uint32_t>::max()) {
        tarjan(lit.toInt());
        recurDepth--;
        lowlink[vertex] = std::min(lowlink[vertex], lowlink[lit.toInt()]);
    } else if (stackIndicator[lit.toInt()])  {
        lowlink[vertex] = std::min(lowlink[vertex], lowlink[lit.toInt()]);
    }
}

inline double SCCFinder::getTotalTime() const
{
    return totalTime;
}

}

#endif //SCCFINDER_H

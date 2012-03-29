/***********************************************************************************
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
**************************************************************************************************/

#ifndef RESTARTTYPECHOOSER_H
#define RESTARTTYPECHOOSER_H

#include "Solver.h"
#include <vector>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "SolverTypes.h"

namespace CMSat {

using std::vector;

class Solver;

/**
@brief Chooses between MiniSat and GLUCOSE restart types&learnt clause evaluation

MiniSat style restart is geometric, and glucose-type is dynamic. MiniSat-type
learnt clause staistic is activity-based, glucose-type is glue-based. This
class takes as input a number of MiniSat restart's end results, computes some
statistics on them, and at the end, tells if we should use one type or the
other. Basically, it masures variable activity stability, number of xors
in the problem, and variable degrees.
*/
class RestartTypeChooser
{
    public:
        RestartTypeChooser(const Solver& s);
        void addInfo();
        RestartType choose();
        void reset();

    private:
        void calcHeap();
        double avg() const;
        std::pair<double, double> countVarsDegreeStDev() const;
        double stdDeviation(vector<uint32_t>& measure) const;

        template<class T>
        void addDegrees(const vec<T*>& cs, vector<uint32_t>& degrees) const;
        void addDegreesBin(vector<uint32_t>& degrees) const;

        const Solver& solver;
        uint32_t topX; ///<The how many is the top X? 100 is default
        uint32_t limit; ///<If top x contains on average this many common varables, we select MiniSat-type
        vector<Var> sameIns;

        vector<Var> firstVars; ///<The top x variables (in terms of var activity)
        vector<Var> firstVarsOld; ///<The previous top x variables (in terms of var activity)
};

inline void RestartTypeChooser::reset()
{
    sameIns.clear();
}

}

#endif //RESTARTTYPECHOOSER_H

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

#ifndef STATESAVER__H
#define STATESAVER__H

#include "Solver.h"

namespace CMSat {

class StateSaver
{
    public:
        StateSaver(Solver& _solver);
        void restore();

    private:
        Solver& solver;
        Heap<Solver::VarOrderLt> backup_order_heap;
        vector<char> backup_polarities;
        vec<uint32_t> backup_activity;
        uint32_t backup_var_inc;
        RestartType backup_restartType;
        double backup_random_var_freq;
        uint64_t backup_propagations;
};

}

#endif //STATESAVER__H

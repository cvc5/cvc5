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

#ifndef GAUSSIANCONFIG_H
#define GAUSSIANCONFIG_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "PackedRow.h"

namespace CMSat
{

class GaussConf
{
    public:

    GaussConf() :
        only_nth_gauss_save(2)
        , decision_until(0)
        , dontDisable(false)
        , noMatrixFind(false)
        , orderCols(true)
        , iterativeReduce(true)
        , maxMatrixRows(1000)
        , minMatrixRows(20)
        , maxNumMatrixes(3)
    {
    }

    //tuneable gauss parameters
    uint32_t only_nth_gauss_save;  //save only every n-th gauss matrix
    uint32_t decision_until; //do Gauss until this level
    bool dontDisable; //If activated, gauss elimination is never disabled
    bool noMatrixFind; //Put all xor-s into one matrix, don't find matrixes
    bool orderCols; //Order columns according to activity
    bool iterativeReduce; //Don't minimise matrix work
    uint32_t maxMatrixRows; //The maximum matrix size -- no. of rows
    uint32_t minMatrixRows; //The minimum matrix size -- no. of rows
    uint32_t maxNumMatrixes; //Maximum number of matrixes
};

}

#endif //GAUSSIANCONFIG_H

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

#ifndef DOUBLEPACKEDROW_H
#define DOUBLEPACKEDROW_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include <stdlib.h>

#include "SolverTypes.h"

namespace CMSat
{
using namespace CMSat;

class DoublePackedRow
{
    private:
        class BitIter {
            public:
                inline void operator=(const lbool toSet)
                {
                    val &= ~((unsigned char)3 << offset);
                    val |= toSet.value << offset;
                }
                
                inline operator lbool() const
                {
                    return lbool((val >> offset) & 3);
                }
                
                inline const bool isUndef() const {
                    return ((lbool)*this).isUndef();
                }
                inline const bool isDef() const {
                    return ((lbool)*this).isDef();
                }
                inline const bool getBool() const {
                    return ((lbool)*this).getBool();
                }
                inline const bool operator==(lbool b) const {
                    return ((lbool)*this) == b;
                }
                inline const bool operator!=(lbool b) const {
                    return ((lbool)*this) != b;
                }
                const lbool operator^(const bool b) const {
                    return ((lbool)*this) ^ b;
                }
                
            private:
                friend class DoublePackedRow;
                inline BitIter(unsigned char& mp, const uint32_t _offset) :
                val(mp)
                , offset(_offset)
                {}
                
                unsigned char& val;
                const uint32_t offset;
        };
        
        class BitIterConst {
             public:
                inline operator lbool() const
                {
                    return lbool((val >> offset) & 3);
                }
                
                inline const bool isUndef() const {
                    return ((lbool)*this).isUndef();
                }
                inline const bool isDef() const {
                    return ((lbool)*this).isDef();
                }
                inline const bool getBool() const {
                    return ((lbool)*this).getBool();
                }
                inline const bool operator==(lbool b) const {
                    return ((lbool)*this) == b;
                }
                inline const bool operator!=(lbool b) const {
                    return ((lbool)*this) != b;
                }
                const lbool operator^(const bool b) const {
                    return ((lbool)*this) ^ b;
                }
                
                
            private:
                friend class DoublePackedRow;
                inline BitIterConst(unsigned char& mp, const uint32_t _offset) :
                val(mp)
                , offset(_offset)
                {}
                
                const unsigned char& val;
                const uint32_t offset;
        };
    
    public:
        DoublePackedRow() :
            numElems(0)
            , mp(NULL)
        {}
        
        uint32_t size() const
        {
            return numElems;
        }
        
        void growTo(const uint32_t newNumElems)
        {
            uint32_t oldSize = numElems/4 + (bool)(numElems % 4);
            uint32_t newSize = newNumElems/4 + (bool)(newNumElems % 4);
            
            if (oldSize >= newSize) {
                numElems = std::max(newNumElems, numElems);
                return;
            }
            
            mp = (unsigned char*)realloc(mp, newSize*sizeof(unsigned char));
            numElems = newNumElems;
        }
        
        inline BitIter operator[](const uint32_t at)
        {
            return BitIter(mp[at/4], (at%4)*2);
        }
        
        inline const BitIterConst operator[](const uint32_t at) const
        {
            return BitIterConst(mp[at/4], (at%4)*2);
        }
        
        inline void push(const lbool val)
        {
            growTo(numElems+1);
            (*this)[numElems-1] = val;
        }
        
        /*void clear(const uint32_t at)
        {
            mp[at/32] &= ~((uint64_t)3 << ((at%32)*2));
        }*/
        
    private:
        
        Var numElems;
        unsigned char *mp;
};

}; //NAMESPACE MINISAT

#endif //DOUBLEPACKEDROW_H

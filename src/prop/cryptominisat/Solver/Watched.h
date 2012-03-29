/***************************************************************************
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
*****************************************************************************/

#ifndef WATCHED_H
#define WATCHED_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

//#define DEBUG_WATCHED

#include "ClauseOffset.h"
#include "SolverTypes.h"
#include <stdio.h>
#include <limits>
#include "constants.h"

namespace CMSat {

/**
@brief An element in the watchlist. Natively contains 2- and 3-long clauses, others are referenced by pointer

This class contains two 32-bit datapieces. They are either used as:
\li One literal, in the case of binary clauses
\li Two literals, in the case of tertiary clauses
\li One blocking literal (i.e. an example literal from the clause) and a clause
offset (as per ClauseAllocator ), in the case of normal clauses
\li A clause offset (as per ClauseAllocator) for xor clauses
*/
class Watched {
    public:
        /**
        @brief Constructor for a long normal clause
        */
        Watched(const ClauseOffset offset, Lit blockedLit)
        {
            data1 = blockedLit.toInt();
            data2 = (uint32_t)1 + ((uint32_t)offset << 2);
        }

        Watched() :
            data1 (std::numeric_limits<uint32_t>::max())
            , data2(std::numeric_limits<uint32_t>::max())
        {}

        /**
        @brief Constructor for an xor-clause
        */
        Watched(const ClauseOffset offset)
        {
            data1 = (uint32_t)offset;
            data2 = (uint32_t)2;
        }

        /**
        @brief Constructor for a binary clause
        */
        Watched(const Lit lit, const bool learnt)
        {
            data1 = lit.toInt();
            data2 = (uint32_t)0 + (((uint32_t)learnt) << 2);
        }

        /**
        @brief Constructor for a 3-long, non-xor clause
        */
        Watched(const Lit lit1, const Lit lit2)
        {
            data1 = lit1.toInt();
            data2 = (uint32_t)3 + (lit2.toInt()<< 2);
        }

        void setNormOffset(const ClauseOffset offset)
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            data2 = (uint32_t)1 + ((uint32_t)offset << 2);
        }

        void setXorOffset(const ClauseOffset offset)
        {
            #ifdef DEBUG_WATCHED
            assert(isXorClause());
            #endif
            data1 = (uint32_t)offset;
        }

        /**
        @brief To update the example literal (blocked literal) of a >3-long normal clause
        */
        void setBlockedLit(const Lit lit)
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            data1 = lit.toInt();
        }

        bool isBinary() const
        {
            return ((data2&3) == 0);
        }

        bool isNonLearntBinary() const
        {
            return (data2 == 0);
        }

        bool isClause() const
        {
            return ((data2&3) == 1);
        }

        bool isXorClause() const
        {
            return ((data2&3) == 2);
        }

        bool isTriClause() const
        {
            return ((data2&3) == 3);
        }

        /**
        @brief Get the sole other lit of the binary clause, or get lit2 of the tertiary clause
        */
        Lit getOtherLit() const
        {
            #ifdef DEBUG_WATCHED
            assert(isBinary() || isTriClause());
            #endif
            return data1AsLit();
        }

        /**
        @brief Set the sole other lit of the binary clause
        */
        void setOtherLit(const Lit lit)
        {
            #ifdef DEBUG_WATCHED
            assert(isBinary() || isTriClause());
            #endif
            data1 = lit.toInt();
        }

        bool getLearnt() const
        {
            #ifdef DEBUG_WATCHED
            assert(isBinary());
            #endif
            return (bool)(data2 >> 2);
        }

        void setLearnt(const bool learnt)
        {
            #ifdef DEBUG_WATCHED
            assert(isBinary());
            assert(learnt == false);
            #endif
            data2 = (uint32_t)0 + (((uint32_t)learnt) << 2);
        }

        /**
        @brief Get the 3rd literal of a 3-long clause
        */
        Lit getOtherLit2() const
        {
            #ifdef DEBUG_WATCHED
            assert(isTriClause());
            #endif
            return data2AsLit();
        }

        /**
        @brief Get example literal (blocked lit) of a normal >3-long clause
        */
        Lit getBlockedLit() const
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            return data1AsLit();
        }

        /**
        @brief Get offset of a >3-long normal clause or of an xor clause (which may be 3-long)
        */
        ClauseOffset getNormOffset() const
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            return (ClauseOffset)(data2 >> 2);
        }

        ClauseOffset getXorOffset() const
        {
            #ifdef DEBUG_WATCHED
            assert(isXorClause());
            #endif
            return (ClauseOffset)(data1);
        }

        void dump(FILE* outfile, const Lit lit) const
        {
            assert(isBinary());
            lit.print(outfile);
            getOtherLit().printFull(outfile);
        }

        void setNormClause()
        {
            data2 = 1;
        }

        #ifdef DUMP_STATS_FULL
        int glue;
        #endif

    private:
        Lit data1AsLit() const
        {
            return (Lit::toLit(data1));
        }

        Lit data2AsLit() const
        {
            return (Lit::toLit(data2>>2));
        }

        uint32_t data1;
        uint32_t data2;
};

/**
@brief Orders the watchlists such that the order is binary, tertiary, normal, xor
*/
struct WatchedSorter
{
    bool operator () (const Watched& x, const Watched& y);
};

inline bool  WatchedSorter::operator () (const Watched& x, const Watched& y)
{
    if (y.isBinary()) return false;
    //y is not binary, but x is, so x must be first
    if (x.isBinary()) return true;

    //from now on, none is binary.
    if (y.isTriClause()) return false;
    if (x.isTriClause()) return true;

    //from now on, none is binary or tertiary
    //don't bother sorting these
    return false;
}

}

#endif //WATCHED_H

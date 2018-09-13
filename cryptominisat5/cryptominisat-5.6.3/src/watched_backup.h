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

#ifndef WATCHED_H
#define WATCHED_H

//#define DEBUG_WATCHED

#include "clabstraction.h"
#include "constants.h"
#include "cloffset.h"
#include "solvertypes.h"

#include <limits>

namespace CMSat {

enum WatchType {
    watch_clause_t = 0
    , watch_binary_t = 1
    , watch_idx_t = 3
};

/**
@brief An element in the watchlist. Natively contains 2- and 3-long clauses, others are referenced by pointer

This class contains two 32-bit datapieces. They are either used as:
\li One literal, in the case of binary clauses
\li Two literals, in the case of tertiary clauses
\li One blocking literal (i.e. an example literal from the clause) and a clause
offset (as per ClauseAllocator ), in the case of long clauses
*/
class Watched {
    public:
        /**
        @brief Constructor for a long (>3) clause
        */
        Watched(const ClOffset offset, Lit blockedLit) :
            data1(blockedLit.toInt())
            , data2(offset)
            , type(watch_clause_t)
        {
        }

        /**
        @brief Constructor for a long (>3) clause
        */
        Watched(const ClOffset offset, cl_abst_type abst) :
            data1(abst)
            , data2(offset)
            , type(watch_clause_t)
        {
        }

        Watched(){}

        /**
        @brief Constructor for a binary clause
        */
        Watched(const Lit lit, const bool red) :
            data1(lit.toInt())
            , type(watch_binary_t)
            , _red(red)
        {
        }

        /**
        @brief Constructor for an Index value
        */
        Watched(const uint32_t idx) :
            data1(idx)
            , type(watch_idx_t)
        {
        }

        /**
        @brief To update the blocked literal of a >3-long normal clause
        */
        void setBlockedLit(const Lit blockedLit)
        {
            #ifdef DEBUG_WATCHED
            assert(type == watch_clause_t);
            #endif
            data1 = blockedLit.toInt();
        }

        WatchType getType() const
        {
            // we rely that WatchType enum is in [0-3] range and fits into type field two bits
            return static_cast<WatchType>(type);
        }

        bool isBin() const
        {
            return (type == watch_binary_t);
        }

        bool isClause() const
        {
            return (type == watch_clause_t);
        }

        bool isIdx() const
        {
            return (type == watch_idx_t);
        }

        uint32_t get_idx() const
        {
            #ifdef DEBUG_WATCHED
            assert(type == watch_idx_t);
            #endif
            return data1;
        }

        /**
        @brief Get the sole other lit of the binary clause, or get lit2 of the tertiary clause
        */
        Lit lit2() const
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            return Lit::toLit(data1);
        }

        /**
        @brief Set the sole other lit of the binary clause
        */
        void setLit2(const Lit lit)
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            data1 = lit.toInt();
        }

        bool red() const
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            return _red;
        }

        void setRed(const bool
        #ifdef DEBUG_WATCHED
        toSet
        #endif
        )
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            assert(red());
            assert(toSet == false);
            #endif
            _red = true;
        }

        void mark_bin_cl()
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            marked = 1;
        }

        void unmark_bin_cl()
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            marked= 0;
        }

        bool bin_cl_marked() const
        {
            #ifdef DEBUG_WATCHED
            assert(isBin());
            #endif
            return marked;
        }

        /**
        @brief Get example literal (blocked lit) of a normal >3-long clause
        */
        Lit getBlockedLit() const
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            return Lit::toLit(data1);
        }

        cl_abst_type getAbst() const
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            return data1;
        }

        /**
        @brief Get offset of a >3-long normal clause or of an xor clause (which may be 3-long)
        */
        ClOffset get_offset() const
        {
            #ifdef DEBUG_WATCHED
            assert(isClause());
            #endif
            return data2;
        }

        bool operator==(const Watched& other) const
        {
            return data1 == other.data1 && data2 == other.data2 && type == other.type
                    && _red == other._red;
        }

        bool operator!=(const Watched& other) const
        {
            return !(*this == other);
        }

        Watched(Watched&& o) noexcept {
            data1 = o.data1;
            data2 = o.data2;
            type = o.type;
            _red = o._red;
            marked = o.marked;
        }

        Watched(const Watched& o) noexcept {
            data1 = o.data1;
            data2 = o.data2;
            type = o.type;
            _red = o._red;
            marked = o.marked;
        }

        Watched& operator=(const Watched& o) noexcept {
            data1 = o.data1;
            data2 = o.data2;
            type = o.type;
            _red = o._red;
            marked = o.marked;
            return *this;
        }

    private:
        uint32_t data1;
        // binary, tertiary or long, as per WatchType
        // currently WatchType is enum with range [0..3] and fits in type
        // in case if WatchType extended type size won't be enough.
        uint32_t data2;
        char type;
        char _red;
        char marked;
};

inline std::ostream& operator<<(std::ostream& os, const Watched& ws)
{

    if (ws.isClause()) {
        os << "Clause offset " << ws.get_offset();
    }

    if (ws.isBin()) {
        os << "Bin lit " << ws.lit2() << " (red: " << ws.red() << " )";
    }

    return os;
}

struct OccurClause {
    OccurClause(const Lit _lit, const Watched _ws) :
        lit(_lit)
        , ws(_ws)
    {}

    OccurClause() :
        lit(lit_Undef)
    {}

    bool operator==(const OccurClause& other) const
    {
        return lit == other.lit && ws == other.ws;
    }

    Lit lit;
    Watched ws;
};

struct WatchSorterBinTriLong {
        bool operator()(const Watched& a, const Watched& b)
        {
            assert(!a.isIdx());
            assert(!b.isIdx());

            //Anything but clause!
            if (a.isClause()) {
                //A is definitely not better than B
                return false;
            }
            if (b.isClause()) {
                //B is clause, A is NOT a clause. So A is better than B.
                return true;
            }

            //Both are BIN
            assert(a.isBin());
            assert(b.isBin());

            if (a.lit2() != b.lit2()) {
                return a.lit2() < b.lit2();
            }

            if (a.red() != b.red()) {
                return !a.red();
            }
            return false;
        }
    };


} //end namespace

#endif //WATCHED_H

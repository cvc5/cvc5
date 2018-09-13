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

#ifndef PROPBY_H
#define PROPBY_H

#include "constants.h"
#include "solvertypes.h"
#include "clause.h"

//#define DEBUG_PROPAGATEFROM

#include "cloffset.h"

namespace CMSat {

enum PropByType {null_clause_t = 0, clause_t = 1, binary_t = 2, tertiary_t = 3};

class PropBy
{
    private:
        uint32_t data1;
        uint32_t data2;

        //0: clause, NULL
        //1: clause, non-null
        //2: binary
        //3: tertiary
        char type;

        char red_step;

    public:
        PropBy() :
            red_step(0)
            , data1(0)
            , type(null_clause_t)
            , data2(0)
        {}

        //Normal clause prop
        explicit PropBy(const ClOffset offset) :
            red_step(0)
            , data1(offset)
            , type(clause_t)
            , data2(0)
        {
            //No roll-over
            /*#ifdef DEBUG_PROPAGATEFROM
            assert(offset == get_offset());
            #endif*/
        }

        //Binary prop
        PropBy(const Lit lit, const bool redStep) :
            red_step(redStep)
            , data1(lit.toInt())
            , type(binary_t)
            , data2(0)
        {
        }

        //For hyper-bin, etc.
        PropBy(
            const Lit lit
            , bool redStep //Step that lead here from ancestor is redundant
            , bool hyperBin //It's a hyper-binary clause
            , bool hyperBinNotAdded //It's a hyper-binary clause, but was never added because all the rest was zero-level
        ) :
            red_step(redStep)
            , data1(lit.toInt())
            , type(binary_t)
            , data2(0)
        {
            //HACK: if we are doing seamless hyper-bin and transitive reduction
            //then if we are at toplevel, .getAncestor()
            //must work, and return lit_Undef, but at the same time, .isNULL()
            //must also work, for conflict generation. So this is a hack to
            //achieve that. What an awful hack.
            if (lit == ~lit_Undef)
                type = null_clause_t;

            data2 = ((uint32_t)hyperBin) << 1
                | ((uint32_t)hyperBinNotAdded) << 2;
        }

        //Tertiary prop
        PropBy(const Lit lit1, const Lit lit2, const bool redStep) :
            red_step(redStep)
            , data1(lit1.toInt())
            , type(tertiary_t)
            , data2(lit2.toInt())
        {
        }

        bool isRedStep() const
        {
            return red_step;
        }

        bool getHyperbin() const
        {
            return data2 & 2U;
        }

        void setHyperbin(bool toSet)
        {
            data2 &= ~2U;
            data2 |= (uint32_t)toSet << 1;
        }

        bool getHyperbinNotAdded() const
        {
            return data2 & 4U;
        }

        void setHyperbinNotAdded(bool toSet)
        {
            data2 &= ~4U;
            data2 |= (uint32_t)toSet << 2;
        }

        Lit getAncestor() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(type == null_clause_t || type == binary_t);
            #endif
            return ~Lit::toLit(data1);
        }

        bool isClause() const
        {
            return type == clause_t;
        }

        PropByType getType() const
        {
            return (PropByType)type;
        }

        Lit lit2() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(type == tertiary_t || type == binary_t);
            #endif
            return Lit::toLit(data1);
        }

        Lit lit3() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(type == tertiary_t);
            #endif
            return Lit::toLit(data2);
        }

        ClOffset get_offset() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isClause());
            #endif
            return data1;
        }

        bool isNULL() const
        {
            return type == null_clause_t;
        }

        bool operator==(const PropBy other) const
        {
            return (type == other.type
                    && red_step == other.red_step
                    && data1 == other.data1
                    && data2 == other.data2
                   );
        }

        bool operator!=(const PropBy other) const
        {
            return !(*this == other);
        }
};

inline std::ostream& operator<<(std::ostream& os, const PropBy& pb)
{
    switch (pb.getType()) {
        case binary_t :
            os << " binary, other lit= " << pb.lit2();
            break;

        case tertiary_t :
            os << " tri, other 2 lits= " << pb.lit2() << " , "<< pb.lit3();
            break;

        case clause_t :
            os << " clause, num= " << pb.get_offset();
            break;

        case null_clause_t :
            os << " NULL";
            break;

        default:
            assert(false);
            break;
    }
    return os;
}

} //end namespace

#endif //PROPBY_H

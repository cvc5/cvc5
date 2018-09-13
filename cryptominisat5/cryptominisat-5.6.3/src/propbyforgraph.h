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

#include "solvertypes.h"
#include "clause.h"
#include "propby.h"
#include "clauseallocator.h"

#ifndef __PROPBYFORGRAPH_H__
#define __PROPBYFORGRAPH_H__

namespace CMSat {

class PropByForGraph
{
    private:
        uint16_t type;
        uint32_t isize;
        Clause* clause;
        Lit lits[3];

    public:
        PropByForGraph(PropBy orig
                    , Lit otherLit
                    , const ClauseAllocator& alloc
        ) :
            type(10)
            , isize(0)
            , clause(NULL)
        {
            if (orig.getType() == binary_t) {
                lits[0] = otherLit;
                lits[1] = orig.lit2();
                type = 1;
                isize = 2;
            }
            if (orig.isClause()) {
                if (orig.isNULL()) {
                    type = 0;
                    isize = 0;
                    clause = NULL;
                    return;
                }
                clause = alloc.ptr(orig.get_offset());
                isize = clause->size();
                type = 0;
            }
        }

        PropByForGraph() :
            type(0)
            , clause(NULL)
        {}

        PropByForGraph(const PropByForGraph& other) :
            type(other.type)
            , isize(other.isize)
            , clause(other.clause)
        {
            memcpy(lits, other.lits, sizeof(Lit)*3);
        }

        PropByForGraph& operator=(const PropByForGraph& other)
        {
            type = other.type,
            isize = other.isize;
            clause = other.clause;
            //delete xorLits;
            memcpy(lits, other.lits, sizeof(Lit)*3);
            return *this;
        }

        uint32_t size() const
        {
            return isize;
        }

        bool isNULL() const
        {
            return type == 0 && clause == NULL;
        }

        bool isClause() const
        {
            return type == 0;
        }

        bool isBin() const
        {
            return type == 1;
        }

        const Clause* getClause() const
        {
            return clause;
        }

        Clause* getClause()
        {
            return clause;
        }

        Lit operator[](const uint32_t i) const
        {
            switch (type) {
                case 0:
                    assert(clause != NULL);
                    return (*clause)[i];

                default :
                    return lits[i];
            }
        }
};

inline std::ostream& operator<<(
    std::ostream& os
    , const PropByForGraph& propByFull
) {

    if (propByFull.isBin()) {
        os << propByFull[0] << " " << propByFull[1];
    } else if (propByFull.isClause()) {
        if (propByFull.isNULL()) os << "null clause";
        else os << *propByFull.getClause();
    }
    return os;
}

} //end namespace

#endif //__PROPBYFORGRAPH_H__

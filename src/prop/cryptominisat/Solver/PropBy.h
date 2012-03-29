/***********************************************************************
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
************************************************************************/

#ifndef PROPBY_H
#define PROPBY_H

#include "SolverTypes.h"
#include "Clause.h"
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER
#include <stdio.h>

//#define DEBUG_PROPAGATEFROM

#include "ClauseOffset.h"
#include "ClauseAllocator.h"

namespace CMSat {

class PropBy
{
    private:
        uint64_t propType:2;
        //0: clause, NULL
        //1: clause, non-null
        //2: binary
        //3: tertiary
        uint64_t data1:30;
        uint64_t data2:32;

    public:
        PropBy() :
            propType(0)
            , data1(0)
            , data2(0)
        {}

        PropBy(ClauseOffset offset) :
            propType(1)
            , data2(offset)
        {
        }

        PropBy(const Lit lit) :
            propType(2)
            , data1(lit.toInt())
        {
        }

        PropBy(const Lit lit1, const Lit lit2) :
            propType(3)
            , data1(lit1.toInt())
            , data2(lit2.toInt())
        {
        }

        bool isClause() const
        {
            return ((propType&2) == 0);
        }

        bool isBinary() const
        {
            return (propType == 2);
        }

        bool isTri() const
        {
            return (propType == 3);
        }

        Lit getOtherLit() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isBinary() || isTri());
            #endif
            return Lit::toLit(data1);
        }

        Lit getOtherLit2() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isTri());
            #endif
            return Lit::toLit(data2);
        }

        ClauseOffset getClause() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isClause());
            #endif
            return data2;
        }

        ClauseOffset getClause()
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isClause());
            #endif
            return data2;
        }

        bool isNULL() const
        {
            if (!isClause()) return false;
            return propType == 0;
        }
};

inline std::ostream& operator<<(std::ostream& os, const PropBy& pb)
{
    if (pb.isBinary()) {
        os << " binary, other lit= " << pb.getOtherLit();
    } else if (pb.isClause()) {
        os << " clause, num= " << pb.getClause();
    } else if (pb.isNULL()) {
        os << " NULL";
    } else if (pb.isTri()) {
        os << " tri, other 2 lits= " << pb.getOtherLit() << " , "<< pb.getOtherLit2();
    }
    return os;
}

class PropByFull
{
    private:
        uint32_t type;
        Clause* clause;
        Lit lits[3];

    public:
        PropByFull(PropBy orig, Lit otherLit, ClauseAllocator& alloc) :
            type(10)
            , clause(NULL)
        {
            if (orig.isBinary() || orig.isTri()) {
                lits[0] = otherLit;
                lits[1] = orig.getOtherLit();
                if (orig.isTri()) {
                    lits[2] = orig.getOtherLit2();
                    type = 2;
                } else {
                    type = 1;
                }
            }
            if (orig.isClause()) {
                type = 0;
                if (orig.isNULL()) {
                    clause = NULL;
                } else {
                    clause = alloc.getPointer(orig.getClause());
                }
            }
        }

        PropByFull() :
            type(10)
        {}

        PropByFull(const PropByFull& other) :
            type(other.type)
            , clause(other.clause)
        {
            memcpy(lits, other.lits, sizeof(Lit)*3);
        }

        uint32_t size() const
        {
            switch (type) {
                case 0 : return clause->size();
                case 1 : return 2;
                case 2 : return 3;
                default:
                    assert(false);
                    return 0;
            }
        }

        bool isNULL() const
        {
            return type == 0 && clause == NULL;
        }

        bool isClause() const
        {
            return type == 0;
        }

        bool isBinary() const
        {
            return type == 1;
        }

        bool isTri() const
        {
            return type == 2;
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
                case 0: {
                    assert(clause != NULL);
                    return (*clause)[i];
                }
                default : {
                    return lits[i];
                }
            }
        }
};

inline std::ostream& operator<<(std::ostream& cout, const PropByFull& propByFull)
{

    if (propByFull.isBinary()) {
        cout << "binary: " << " ? , " << propByFull[1];
    } else if (propByFull.isTri()) {
        cout << "tri: " << " ? , " <<propByFull[1] << " , " << propByFull[2];
    } else if (propByFull.isClause()) {
        if (propByFull.isNULL()) cout << "null clause";
        else cout << "clause:" << *propByFull.getClause();
    }
    return cout;
}

}

#endif //PROPBY_H

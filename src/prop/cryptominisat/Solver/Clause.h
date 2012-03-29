/*****************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
glucose -- Gilles Audemard, Laurent Simon (2008)
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Original code by MiniSat and glucose authors are under an MIT licence.
Modifications for CryptoMiniSat are under GPLv3 licence.
******************************************************************************/

#ifndef CLAUSE_H
#define CLAUSE_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include <cstdio>
#include <vector>
#include <sys/types.h>
#include <string.h>

#include "SolverTypes.h"
#include "constants.h"
#include "Watched.h"
#include "Alg.h"
#include "constants.h"

namespace CMSat {

template <class T>
uint32_t calcAbstraction(const T& ps) {
    uint32_t abstraction = 0;
    for (uint32_t i = 0; i != ps.size(); i++)
        abstraction |= 1 << (ps[i].var() & 31);
    return abstraction;
}

class MatrixFinder;
class ClauseAllocator;

/**
@brief Holds a clause. Does not allocate space for literals

Literals are allocated by an external allocator that allocates enough space
for the class that it can hold the literals as well. I.e. it malloc()-s
    sizeof(Clause)+LENGHT*sizeof(Lit)
to hold the clause.
*/
struct Clause
{
protected:

    uint32_t isLearnt:1; ///<Is the clause a learnt clause?
    uint32_t changed:1; ///<Var inside clause has been changed
    /**
    @brief Is the XOR equal to 1 or 0?

    i.e. "a + b" = TRUE or FALSE? -- we only have variables inside xor clauses,
    so this is important to know

    NOTE: ONLY set if the clause is an xor clause.
    */
    uint32_t isXorEqualFalse:1;
    uint32_t isXorClause:1; ///< Is the clause an XOR clause?
    uint32_t isRemoved:1; ///<Is this clause queued for removal because of usless binary removal?
    uint32_t isFreed:1; ///<Has this clause been marked as freed by the ClauseAllocator ?
    uint32_t glue:MAX_GLUE_BITS;    ///<Clause glue -- clause activity according to GLUCOSE
    uint32_t mySize:18; ///<The current size of the clause

    float miniSatAct; ///<Clause activity according to MiniSat

    uint32_t abst; //Abstraction of clause

#ifdef _MSC_VER
public:
#endif //_MSC_VER
    template<class V>
    Clause(const V& ps, const bool learnt)
    {
        isFreed = false;
        glue = 0; //To stop valgrind from complaining
        isXorEqualFalse = false; //To stop valgrind from complaining
        isXorClause = false;
        assert(ps.size() > 2);
        mySize = ps.size();
        isLearnt = learnt;
        isRemoved = false;

        assert(ps.size() > 0);
        memcpy(getData(), ps.getData(), ps.size()*sizeof(Lit));
        miniSatAct = 0;
        setChanged();
    }

public:
    friend class ClauseAllocator;

    uint32_t size() const
    {
        return mySize;
    }

    bool getChanged() const
    {
        return changed;
    }

    void setChanged()
    {
        changed = 1;
    }

    void unsetChanged()
    {
        changed = 0;
    }

    void shrink (const uint32_t i)
    {
        assert(i <= size());
        mySize -= i;
        if (i > 0)
            setChanged();
    }

    void pop()
    {
        shrink(1);
    }

    bool isXor() const
    {
        return isXorClause;
    }

    bool learnt() const
    {
        return isLearnt;
    }

    float& getMiniSatAct()
    {
        return miniSatAct;
    }

    void setMiniSatAct(const float newMiniSatAct)
    {
        miniSatAct = newMiniSatAct;
    }

    const float& getMiniSatAct() const
    {
        return miniSatAct;
    }

    Lit& operator [] (const uint32_t i)
    {
        return *(getData() + i);
    }

    const Lit& operator [] (const uint32_t i) const
    {
        return *(getData() + i);
    }

    void setGlue(const uint32_t newGlue)
    {
        assert(newGlue <= MAX_THEORETICAL_GLUE);
        glue = newGlue;
    }

    uint32_t getGlue() const
    {
        return glue;
    }

    void makeNonLearnt()
    {
        assert(isLearnt);
        isLearnt = false;
    }

    void makeLearnt(const uint32_t newGlue, const float newMiniSatAct)
    {
        glue = newGlue;
        miniSatAct = newMiniSatAct;
        isLearnt = true;
    }

    inline void strengthen(const Lit p)
    {
        remove(*this, p);
        setChanged();
    }

    void calcAbstractionClause()
    {
        abst = calcAbstraction(*this);
    }

    uint32_t getAbst() const
    {
        return abst;
    }

    const Lit* getData() const
    {
        return (Lit*)((char*)this + sizeof(Clause));
    }

    Lit* getData()
    {
        return (Lit*)((char*)this + sizeof(Clause));
    }

    const Lit* getDataEnd() const
    {
        return getData()+size();
    }

    Lit* getDataEnd()
    {
        return getData() + size();
    }

    void print(FILE* to = stdout) const
    {
        plainPrint(to);
        fprintf(to, "c clause learnt %s glue %d miniSatAct %.3f\n", (learnt() ? "yes" : "no"), getGlue(), getMiniSatAct());
    }

    void plainPrint(FILE* to = stdout) const
    {
        for (uint32_t i = 0; i < size(); i++) {
            if ((getData()+i)->sign()) fprintf(to, "-");
            fprintf(to, "%d ", (getData()+i)->var() + 1);
        }
        fprintf(to, "0\n");
    }

    void setRemoved()
    {
        isRemoved = true;
    }

    bool getRemoved() const
    {
        return isRemoved;
    }

    void setFreed()
    {
        isFreed = true;
    }

    bool getFreed() const
    {
        return isFreed;
    }

    void takeMaxOfStats(Clause& other)
    {
        if (other.getGlue() < getGlue())
            setGlue(other.getGlue());
        if (other.getMiniSatAct() > getMiniSatAct())
            setMiniSatAct(other.getMiniSatAct());
    }
};

/**
@brief Holds an xor clause. Similarly to Clause, it cannot be directly used

The space is not allocated for the literals. See Clause for details
*/
class XorClause : public Clause
{
protected:
    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    XorClause(const V& ps, const bool xorEqualFalse) :
        Clause(ps, false)
    {
        isXorEqualFalse = xorEqualFalse;
        isXorClause = true;
    }

public:
    friend class ClauseAllocator;

    inline bool xorEqualFalse() const
    {
        return isXorEqualFalse;
    }

    inline void invert(const bool b)
    {
        isXorEqualFalse ^= b;
    }

    void print(FILE* to = stdout) const
    {
        plainPrint(to);
        fprintf(to, "c clause learnt %s glue %d miniSatAct %.3f\n", (learnt() ? "yes" : "no"), getGlue(), getMiniSatAct());
    }

    void plainPrint(FILE* to = stdout) const
    {
        fprintf(to, "x");
        if (xorEqualFalse())
            fprintf(to, "-");
        for (uint32_t i = 0; i < size(); i++) {
            fprintf(to, "%d ", this->operator[](i).var() + 1);
        }
        fprintf(to, "0\n");
    }

    friend class MatrixFinder;
};

inline std::ostream& operator<<(std::ostream& cout, const Clause& cl)
{
    for (uint32_t i = 0; i < cl.size(); i++) {
        cout << cl[i] << " ";
    }
    return cout;
}

inline std::ostream& operator<<(std::ostream& cout, const XorClause& cl)
{
    cout << "x";
    for (uint32_t i = 0; i < cl.size(); i++) {
        cout << cl[i].var() + 1 << " ";
    }
    if (cl.xorEqualFalse()) cout << " =  false";
    else cout << " = true";

    return cout;
}

}

#endif //CLAUSE_H

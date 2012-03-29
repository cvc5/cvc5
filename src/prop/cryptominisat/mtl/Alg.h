/*******************************************************************************************[Alg.h]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef ALG_H
#define ALG_H

#include <iostream>
#include "Vec.h"
#include "../Solver/SolverTypes.h"
#include "../Solver/Watched.h"

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER


// Useful functions on vectors

namespace CMSat {

template<class V, class T>
static inline void remove(V& ts, const T& t)
{
    uint32_t j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    assert(j < ts.size());
    for (; j < ts.size()-1; j++) ts[j] = ts[j+1];
    ts.pop();
}

template<class V>
static inline uint32_t removeAll(V& ts, const Var t)
{
    Lit* i = ts.getData();
    Lit* j = i;
    for (Lit *end = ts.getDataEnd(); i != end; i++) {
        if (i->var() != t) {
            *j++ = *i;
        }
    }
    ts.shrink(i-j);

    return (i-j);
}

template<class V, class T>
static inline void removeW(V& ts, const T& t)
{
    uint32_t j = 0;
    for (; j < ts.size() && ts[j].clause != t; j++);
    assert(j < ts.size());
    for (; j < ts.size()-1; j++) ts[j] = ts[j+1];
    ts.pop();
}

template<class V, class T>
static inline bool find(V& ts, const T& t)
{
    uint32_t j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    return j < ts.size();
}

template<class V, class T>
static inline bool findW(V& ts, const T& t)
{
    uint32_t j = 0;
    for (; j < ts.size() && ts[j].clause != t; j++);
    return j < ts.size();
}


//Normal clause
static bool    findWCl(const vec<Watched>& ws, const ClauseOffset c);
static void    removeWCl(vec<Watched> &ws, const ClauseOffset c);

//Binary clause
static bool    findWBin(const vec<vec<Watched> >& wsFull, const Lit lit1, const Lit impliedLit);
static bool    findWBin(const vec<vec<Watched> >& wsFull, const Lit lit1, const Lit impliedLit, const bool learnt);
static void    removeWBin(vec<Watched> &ws, const Lit impliedLit, const bool learnt);
static void    removeWTri(vec<Watched> &ws, const Lit lit1, Lit lit2);
static std::pair<uint32_t, uint32_t>  removeWBinAll(vec<Watched> &ws, const Lit impliedLit);
static Watched& findWatchedOfBin(vec<vec<Watched> >& wsFull, const Lit lit1, const Lit lit2, const bool learnt);
static Watched& findWatchedOfBin(vec<vec<Watched> >& wsFull, const Lit lit1, const Lit lit2);

//Xor Clause
static bool    findWXCl(const vec<Watched>& ws, const ClauseOffset c);
static void    removeWXCl(vec<Watched> &ws, const ClauseOffset c);

//////////////////
// NORMAL Clause
//////////////////
static inline bool findWCl(const vec<Watched>& ws, const ClauseOffset c)
{
    vec<Watched>::const_iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isClause() || i->getNormOffset() != c); i++);
    return i != end;
}

static inline void removeWCl(vec<Watched> &ws, const ClauseOffset c)
{
    vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isClause() || i->getNormOffset() != c); i++);
    assert(i != end);
    vec<Watched>::iterator j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

//////////////////
// XOR Clause
//////////////////
static inline bool findWXCl(const vec<Watched>& ws, const ClauseOffset c)
{
    vec<Watched>::const_iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isXorClause() || i->getXorOffset() != c); i++);
    return i != end;
}

static inline void removeWXCl(vec<Watched> &ws, const ClauseOffset c)
{
    vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isXorClause() || i->getXorOffset() != c); i++);
    assert(i != end);
    vec<Watched>::iterator j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

//////////////////
// TRI Clause
//////////////////

static inline bool findWTri(const vec<Watched> &ws, const Lit lit1, const Lit lit2)
{
    vec<Watched>::const_iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isTriClause() || i->getOtherLit() != lit1 || i->getOtherLit2() != lit2); i++);
    return i != end;
}

static inline void removeWTri(vec<Watched> &ws, const Lit lit1, const Lit lit2)
{
    vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isTriClause() || i->getOtherLit() != lit1 || i->getOtherLit2() != lit2); i++);
    assert(i != end);
    vec<Watched>::iterator j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

//////////////////
// BINARY Clause
//////////////////
static inline bool findWBin(const vec<vec<Watched> >& wsFull, const Lit lit1, const Lit impliedLit)
{
    vec<Watched>::const_iterator i = wsFull[(~lit1).toInt()].getData();
    vec<Watched>::const_iterator end = wsFull[(~lit1).toInt()].getDataEnd();
    for (; i != end && (!i->isBinary() || i->getOtherLit() != impliedLit); i++);
    return i != end;
}

static inline bool findWBin(const vec<vec<Watched> >& wsFull, const Lit lit1, const Lit impliedLit, const bool learnt)
{
    vec<Watched>::const_iterator i = wsFull[(~lit1).toInt()].getData();
    vec<Watched>::const_iterator end = wsFull[(~lit1).toInt()].getDataEnd();
    for (; i != end && (!i->isBinary() || i->getOtherLit() != impliedLit || i->getLearnt() != learnt); i++);
    return i != end;
}

static inline void removeWBin(vec<Watched> &ws, const Lit impliedLit, const bool learnt)
{
    vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd();
    for (; i != end && (!i->isBinary() || i->getOtherLit() != impliedLit || i->getLearnt() != learnt); i++);
    assert(i != end);
    vec<Watched>::iterator j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

static inline std::pair<uint32_t, uint32_t>  removeWBinAll(vec<Watched> &ws, const Lit impliedLit)
{
    uint32_t removedLearnt = 0;
    uint32_t removedNonLearnt = 0;

    vec<Watched>::iterator i = ws.getData();
    vec<Watched>::iterator j = i;
    for (vec<Watched>::iterator end = ws.getDataEnd(); i != end; i++) {
        if (!i->isBinary() || i->getOtherLit() != impliedLit)
            *j++ = *i;
        else {
            if (i->getLearnt())
                removedLearnt++;
            else
                removedNonLearnt++;
        }
    }
    ws.shrink_(i-j);

    return std::make_pair(removedLearnt, removedNonLearnt);
}

static inline Watched& findWatchedOfBin(vec<vec<Watched> >& wsFull, const Lit lit1, const Lit lit2, const bool learnt)
{
    vec<Watched>& ws = wsFull[(~lit1).toInt()];
    for (vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
        if (i->isBinary() && i->getOtherLit() == lit2 && i->getLearnt() == learnt)
            return *i;
    }

    assert(false);
    return *ws.getData();
}

static inline Watched& findWatchedOfBin(vec<vec<Watched> >& wsFull, const Lit lit1, const Lit lit2)
{
    vec<Watched>& ws = wsFull[(~lit1).toInt()];
    for (vec<Watched>::iterator i = ws.getData(), end = ws.getDataEnd(); i != end; i++) {
        if (i->isBinary() && i->getOtherLit() == lit2)
            return *i;
    }

    assert(false);
    return *ws.getData();
}

}

#endif //__ALG_H__

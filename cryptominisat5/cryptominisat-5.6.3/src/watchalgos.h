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

#ifndef __WATCHALGOS_H__
#define __WATCHALGOS_H__

#include "watched.h"
#include "watcharray.h"
#include "clauseallocator.h"

namespace CMSat {

//////////////////
// NORMAL Clause
//////////////////
static inline bool findWCl(watch_subarray_const ws, const ClOffset c)
{
    const Watched* i = ws.begin(), *end = ws.end();
    for (; i != end && (!i->isClause() || i->get_offset() != c); i++);
    return i != end;
}

static inline void removeWCl(watch_subarray ws, const ClOffset c)
{
    Watched* i = ws.begin(), *end = ws.end();
    for (; i != end && (!i->isClause() || i->get_offset() != c); i++);
    assert(i != end);
    Watched* j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

//////////////////
// BINARY Clause
//////////////////

inline void removeWBin(
    watch_array &wsFull
    , const Lit lit1
    , const Lit lit2
    , const bool red
) {
    watch_subarray ws = wsFull[lit1];
    Watched *i = ws.begin(), *end = ws.end();
    for (; i != end && (
        !i->isBin()
        || i->lit2() != lit2
        || i->red() != red
    ); i++);

    assert(i != end);
    Watched *j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

inline void removeWBin_change_order(
    watch_array &wsFull
    , const Lit lit1
    , const Lit lit2
    , const bool red
) {
    watch_subarray ws = wsFull[lit1];
    Watched *i = ws.begin(), *end = ws.end();
    for (; i != end && (
        !i->isBin()
        || i->lit2() != lit2
        || i->red() != red
    ); i++);

    assert(i != end);
    *i = ws[ws.size()-1];
    ws.shrink_(1);
}

inline bool removeWBin_except_marked(
    watch_array &wsFull
    , const Lit lit1
    , const Lit lit2
    , const bool red
) {
    watch_subarray ws = wsFull[lit1];
    Watched *i = ws.begin(), *end = ws.end();
    for (; i != end && (
        !i->isBin()
        || i->lit2() != lit2
        || i->red() != red
    ); i++);
    assert(i != end);

    if (i->bin_cl_marked()) {
        return false;
    }

    Watched *j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);

    return true;
}

inline const Watched& findWatchedOfBin(
    const watch_array& wsFull
    , const Lit lit1
    , const Lit lit2
    , const bool red
) {
    watch_subarray_const ws = wsFull[lit1];
    for (const Watched *i = ws.begin(), *end = ws.end(); i != end; i++) {
        if (i->isBin() && i->lit2() == lit2 && i->red() == red)
            return *i;
    }

    assert(false);
    return *ws.begin();
}

inline Watched& findWatchedOfBin(
    watch_array& wsFull
    , const Lit lit1
    , const Lit lit2
    , const bool red
) {
    watch_subarray ws = wsFull[lit1];
    for (Watched *i = ws.begin(), *end = ws.end(); i != end; i++) {
        if (i->isBin() && i->lit2() == lit2 && i->red() == red)
            return *i;
    }

    assert(false);
    return *ws.begin();
}

static inline void removeWXCl(watch_array& wsFull
    , const Lit lit
    , const ClOffset offs
) {
    watch_subarray ws = wsFull[lit];
    Watched *i = ws.begin(), *end = ws.end();
    for (; i != end && (!i->isClause() || i->get_offset() != offs); i++);
    assert(i != end);
    Watched *j = i;
    i++;
    for (; i != end; j++, i++) *j = *i;
    ws.shrink_(1);
}

} //end namespace


#endif //__WATCHALGOS_H__

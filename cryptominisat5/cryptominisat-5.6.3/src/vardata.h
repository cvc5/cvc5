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

#ifndef __VARDATA_H__
#define __VARDATA_H__

#include "constants.h"
#include "propby.h"
#include "avgcalc.h"

namespace CMSat
{

struct VarData
{
    ///contains the decision level at which the assignment was made.
    uint32_t level = 0;

    uint32_t cancelled = 0;
    uint32_t last_picked = 0;
    uint32_t conflicted = 0;

    //Reason this got propagated. NULL means decision/toplevel
    PropBy reason = PropBy();

    ///The preferred polarity of each variable.
    bool polarity = false;

    ///Whether var has been eliminated (var-elim, different component, etc.)
    Removed removed = Removed::none;
    bool is_bva = false;
    bool added_for_xor = false;
};

}

#endif //__VARDATA_H__

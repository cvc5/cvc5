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

#ifndef __TOUCHLIST_H__
#define __TOUCHLIST_H__

#include <vector>
#include "solvertypes.h"

namespace CMSat {

class TouchList
{
public:
    void touch(const Lit lit)
    {
        touch(lit.var());
    }

    template<typename T, typename... Targs>
    void touch(T value, Targs... Fargs) // recursive variadic function
    {
        touch(value);
        touch(Fargs...);
    }

    void touch(const vector<Lit>& lits)
    {
        for(const Lit lit: lits)
            touch(lit.var());
    }

    void touch(const uint32_t var)
    {
        if (touchedBitset.size() <= var)
            touchedBitset.resize(var+1, 0);

        if (touchedBitset[var] == 0) {
            touched.push_back(var);
            touchedBitset[var] = 1;
        }
    }

    const vector<uint32_t>& getTouchedList() const
    {
        return touched;
    }

    void clear()
    {
        //Clear touchedBitset
        for(vector<uint32_t>::const_iterator
            it = touched.begin(), end = touched.end()
            ; it != end
            ; ++it
        ) {
            touchedBitset[*it] = 0;
        }

        //Clear touched
        touched.clear();
    }

    size_t mem_used() const
    {
        uint64_t mem = 0;
        mem += touched.capacity()*sizeof(uint32_t);
        mem += touchedBitset.capacity()*sizeof(char);

        return mem;
    }

    void shrink_to_fit()
    {
        touched.clear();
        touched.shrink_to_fit();
        touchedBitset.clear();
        touchedBitset.shrink_to_fit();
    }

private:
    vector<uint32_t> touched;
    vector<char> touchedBitset;
};


class TouchListLit
{
public:
    void touch(const Lit lit)
    {
        touch(lit.toInt());
    }

    template<typename T, typename... Targs>
    void touch(T value, Targs... Fargs) // recursive variadic function
    {
        touch(value);
        touch(Fargs...);
    }

    void touch(const vector<Lit>& lits)
    {
        for(const Lit lit: lits)
            touch(lit);
    }

    void touch(const uint32_t var)
    {
        if (touchedBitset.size() <= var)
            touchedBitset.resize(var+1, 0);

        if (touchedBitset[var] == 0) {
            touched.push_back(var);
            touchedBitset[var] = 1;
        }
    }

    const vector<uint32_t>& getTouchedList() const
    {
        return touched;
    }

    void clear()
    {
        //Clear touchedBitset
        for(vector<uint32_t>::const_iterator
            it = touched.begin(), end = touched.end()
            ; it != end
            ; ++it
        ) {
            touchedBitset[*it] = 0;
        }

        //Clear touched
        touched.clear();
    }

    size_t mem_used() const
    {
        uint64_t mem = 0;
        mem += touched.capacity()*sizeof(uint32_t);
        mem += touchedBitset.capacity()*sizeof(char);

        return mem;
    }

    void shrink_to_fit()
    {
        touched.clear();
        touched.shrink_to_fit();
        touchedBitset.clear();
        touchedBitset.shrink_to_fit();
    }

private:
    vector<uint32_t> touched;
    vector<char> touchedBitset;
};


} //end namespace

#endif //__TOUCHLIST_H__

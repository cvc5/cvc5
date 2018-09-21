/*************************************************************
MiniSat       --- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat --- Copyright (c) 2014, Mate Soos

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
***************************************************************/

#ifndef __WATCHARRAY_H__
#define __WATCHARRAY_H__

#include "watched.h"
#include "Vec.h"
#include <vector>

namespace CMSat {
using std::vector;

typedef vec<Watched>& watch_subarray;
typedef const vec<Watched>& watch_subarray_const;

class watch_array
{
public:
    vec<vec<Watched> > watches;
    vector<Lit> smudged_list;
    vector<char> smudged;

    void smudge(const Lit lit) {
        if (!smudged[lit.toInt()]) {
            smudged_list.push_back(lit);
            smudged[lit.toInt()] = true;
        }
    }

    const vector<Lit>& get_smudged_list() const {
        return smudged_list;
    }

    void clear_smudged()
    {
        for(const Lit lit: smudged_list) {
            assert(smudged[lit.toInt()]);
            smudged[lit.toInt()] = false;
        }
        smudged_list.clear();
    }

    watch_subarray operator[](Lit pos)
    {
        return watches[pos.toInt()];
    }

    watch_subarray at(size_t pos)
    {
        assert(watches.size() > pos);
        return watches[pos];
    }

    watch_subarray_const operator[](Lit at) const
    {
        return watches[at.toInt()];
    }

    watch_subarray_const at(size_t pos) const
    {
        assert(watches.size() > pos);
        return watches[pos];
    }

    void resize(const size_t new_size)
    {
        assert(smudged_list.empty());
        if (watches.size() < new_size) {
            watches.growTo(new_size);
        } else {
            watches.shrink(watches.size()-new_size);
        }
        smudged.resize(new_size, false);
    }

    void insert(uint32_t num)
    {
        smudged.insert(smudged.end(), num, false);
        watches.insert(num);
    }

    size_t mem_used() const
    {
        double mem = watches.capacity()*sizeof(vec<Watched>);
        for(size_t i = 0; i < watches.size(); i++) {
            //1.2 is overhead
            mem += (double)watches[i].capacity()*(double)sizeof(Watched)*1.2;
        }
        mem += smudged.capacity()*sizeof(char);
        mem += smudged_list.capacity()*sizeof(Lit);
        return mem;
    }

    size_t size() const
    {
        return watches.size();
    }

    void prefetch(const size_t at) const
    {
        __builtin_prefetch(watches[at].data);
    }
    typedef vec<Watched>* iterator;
    typedef const vec<Watched>* const_iterator;

    iterator begin()
    {
        return watches.begin();
    }

    iterator end()
    {
        return watches.end();
    }

    const_iterator begin() const
    {
        return watches.begin();
    }

    const_iterator end() const
    {
        return watches.end();
    }

    void consolidate()
    {
        /*for(auto& ws: watches) {
            ws.shrink_to_fit();
        }*/
        watches.shrink_to_fit();
    }

    void print_stat()
    {
    }

    size_t mem_used_alloc() const
    {
        size_t mem = 0;
        for(auto& ws: watches) {
            mem += ws.capacity()*sizeof(Watched);
        }

        return mem;
    }

    size_t mem_used_array() const
    {
        size_t mem = 0;
        mem += watches.capacity()*sizeof(vector<Watched>);
        mem += sizeof(watch_array);
        return mem;
    }
};

inline void swap(watch_subarray a, watch_subarray b)
{
    a.swap(b);
}


} //End of namespace

#endif //__WATCHARRAY_H__

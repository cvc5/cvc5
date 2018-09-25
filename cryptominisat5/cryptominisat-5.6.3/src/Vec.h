/*******************************************************************************************[Vec.h]
Copyright (c) 2003-2007, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef Vec_h
#define Vec_h

#include <cassert>
#include <new>
#include <cstdint>
#include <limits>
#include <utility>

#include "XAlloc.h"

namespace CMSat {

//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T>
class vec {
public:
    T*  data;
    T* begin()
    {
        return data;
    }
    T* end()
    {
        return data + sz;
    }

    const T* begin() const
    {
        return data;
    }
    const T* end() const
    {
        return data + sz;
    }
private:
    uint32_t sz;
    uint32_t cap;

    // Don't allow copying (error prone):
    vec<T>&  operator = (vec<T>& /*other*/)
    {
        assert(0);
        return *this;
    }
    vec      (vec<T>& /*other*/)
    {
        assert(0);
    }

    // Helpers for calculating next capacity:
    static inline uint32_t  imax   (int32_t x, int32_t y)
    {
        int32_t mask = (y - x) >> (sizeof(uint32_t) * 8 - 1);
        return (x & mask) + (y & (~mask));
    }

public:
    // Constructors:
    vec()                       : data(NULL) , sz(0)   , cap(0)    { }
    explicit vec(uint32_t size)      : data(NULL) , sz(0)   , cap(0)
    {
        growTo(size);
    }
    vec(uint32_t size, const T& pad) : data(NULL) , sz(0)   , cap(0)
    {
        growTo(size, pad);
    }
    ~vec()
    {
        clear(true);
    }

    // Size operations:
    uint32_t      size() const
    {
        return sz;
    }
    void     shrink   (uint32_t nelems)
    {
        assert(nelems <= sz);
        for (uint32_t i = 0; i < nelems; i++) {
            sz--, data[sz].~T();
        }
    }
    void     shrink_  (uint32_t nelems)
    {
        assert(nelems <= sz);
        sz -= nelems;
    }
    uint32_t      capacity () const
    {
        return cap;
    }
    void     capacity (int32_t min_cap);
    void     growTo   (uint32_t size);
    void     growTo   (uint32_t size, const T& pad);
    void     clear    (bool dealloc = false);

    // Stack interface:
    void     push  ()
    {
        if (sz == cap) {
            capacity(sz + 1);
        }
        new (&data[sz]) T();
        sz++;
    }
    void     push  (const T& elem)
    {
        if (sz == cap) {
            capacity(sz + 1);
        }
        data[sz++] = elem;
    }
    void     push_ (const T& elem)
    {
        assert(sz < cap);
        data[sz++] = elem;
    }
    void     pop   ()
    {
        assert(sz > 0);
        sz--, data[sz].~T();
    }
    // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const T& last  () const
    {
        return data[sz - 1];
    }
    T&       last  ()
    {
        return data[sz - 1];
    }

    // Vector interface:
    const T& operator [] (uint32_t index) const
    {
        return data[index];
    }
    T&       operator [] (uint32_t index)
    {
        return data[index];
    }

    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const
    {
        copy.clear();
        copy.growTo(sz);
        for (uint32_t i = 0; i < sz; i++) {
            copy[i] = data[i];
        }
    }
    void moveTo(vec<T>& dest)
    {
        dest.clear(true);
        dest.data = data;
        dest.sz = sz;
        dest.cap = cap;
        data = NULL;
        sz = 0;
        cap = 0;
    }
    void swap(vec<T>& dest)
    {
        std::swap(dest.data, data);
        std::swap(dest.sz, sz);
        std::swap(dest.cap, cap);
    }

    void resize(uint32_t s) {
        if (s < sz) {
            shrink(sz - s);
        } else {
            growTo(s);
        }
    }

    void insert(uint32_t num)
    {
        growTo(sz+num);
    }

    bool empty() const
    {
        return sz == 0;
    }

    void shrink_to_fit()
    {
        if (sz == 0) {
            free(data);
            cap = 0;
            data = NULL;
            return;
        }

        T* data2 = (T*)realloc(data, sz*sizeof(T));
        if (data2 == 0) {
            //We just keep the size then
            return;
        }
        data = data2;
        cap = sz;
     }
};


template<class T>
void vec<T>::capacity(int32_t min_cap)
{
    if ((int32_t)cap >= min_cap) {
        return;
    }

    // NOTE: grow by approximately 3/2
    uint32_t add = imax((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);
    if (add > std::numeric_limits<uint32_t>::max() - cap
        || (((data = (T*)::realloc(data, (cap += (uint32_t)add) * sizeof(T))) == NULL)
            && errno == ENOMEM)
    ) {
        throw std::bad_alloc();
    }
}


template<class T>
void vec<T>::growTo(uint32_t size, const T& pad)
{
    if (sz >= size) {
        return;
    }
    capacity(size);
    for (uint32_t i = sz; i < size; i++) {
        data[i] = pad;
    }
    sz = size;
}


template<class T>
void vec<T>::growTo(uint32_t size)
{
    if (sz >= size) {
        return;
    }
    capacity(size);
    for (uint32_t i = sz; i < size; i++) {
        new (&data[i]) T();
    }
    sz = size;
}


template<class T>
void vec<T>::clear(bool dealloc)
{
    if (data != NULL) {
        for (uint32_t i = 0; i < sz; i++) {
            data[i].~T();
        }
        sz = 0;
        if (dealloc) {
            free(data), data = NULL, cap = 0;
        }
    }
}

//=================================================================================================
}

#endif

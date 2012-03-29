/*******************************************************************************************
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2010-2011, Mate Soos (modifications to original MiniSat implementation)

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
********************************************************************************************/

#ifndef VEC_H
#define VEC_H

#include <cstdlib>
#include <cassert>
#include <iostream>
#include <new>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include <string.h>

namespace CMSat {

// Automatically resizable arrays
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)
template<class T> class vec {
    T*  data;
    uint32_t sz;
    uint32_t cap;

    void     init(uint32_t size, const T& pad);
    void     grow(uint32_t min_cap);

    // Don't allow copying (error prone):
    vec<T>&  operator = (vec<T>& other) { assert(0); return *this; }
             //vec        (vec<T>& other) { assert(0); }

    static inline uint32_t imax(int x, int y) {
        int mask = (y-x) >> (sizeof(int)*8-1);
        return (x&mask) + (y&(~mask)); }

    void     myCopy (const vec<T>& other);

public:
    // Types:
    typedef uint32_t Key;
    typedef T   Datum;

    // Constructors:
    vec(void)                        : data(NULL) , sz(0)   , cap(0)    { }
    vec(uint32_t size)               : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    vec(uint32_t size, const T& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
    vec(T* array, uint32_t size)     : data(array), sz(size), cap(size) { }      // (takes ownership of array -- will be deallocated with 'free()')
    vec(const vec<T>& other)         : data(NULL) , sz(0)   , cap(0)    { myCopy(other); }
   ~vec(void)                                                      { clear(true); }

    // Ownership of underlying array:
    T*       release  (void)           { T* ret = data; data = NULL; sz = 0; cap = 0; return ret; }
    const T* getData() const {return data; }
    const T* getDataEnd() const {return data + size(); }
    T* getData() {return data; }
    T* getDataEnd() {return data + size(); }

    // Size operations:
    uint32_t size   (void) const       { return sz; }
    void     shrink (uint32_t nelems)  { assert(nelems <= sz); for (uint32_t i = 0; i != nelems; i++) sz--, data[sz].~T(); }
    void     shrink_(uint32_t nelems)  { assert(nelems <= sz); sz -= nelems; }
    void     pop    (void)             { sz--, data[sz].~T(); }
    void     growTo (uint32_t size);
    void     growTo (uint32_t size, const T& pad);
    void     clear  (bool dealloc = false);
    void     capacity (uint32_t size) { grow(size); }
    bool empty() const {return size() == 0;}

    typedef T* iterator;
    typedef const T* const_iterator;

    // Stack interface:
    void     reserve(uint32_t res)     { if (cap < res) {cap = res; data = (T*)realloc(data, cap * sizeof(T));}}
    void     push  (void)
    {
        if (sz == cap) {
            grow(cap+1);
        }
        new (&data[sz]) T();
        sz++;
    }
    void     push  (const T& elem)
    {
        if (sz == cap) {
            grow(cap+1);
        }
        data[sz++] = elem;
    }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const T& operator [] (uint32_t index) const  { return data[index]; }
    T&       operator [] (uint32_t index)        { return data[index]; }


    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const { copy.clear(); copy.growTo(sz); for (uint32_t i = 0; i != sz; i++) new (&copy[i]) T(data[i]); }
    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }
};

template<class T>
void vec<T>::grow(uint32_t min_cap) {
    if (min_cap <= cap) return;
    if (cap == 0) cap = (min_cap >= 2) ? min_cap : 2;
    else          do cap = (cap*3+1) >> 1; while (cap < min_cap);
    data = (T*)realloc(data, cap * sizeof(T));
}

template<class T>
void vec<T>::growTo(uint32_t size, const T& pad) {
    if (sz >= size) return;
    grow(size);
    for (uint32_t i = sz; i != size; i++) new (&data[i]) T(pad);
    sz = size; }

template<class T>
void vec<T>::growTo(uint32_t size) {
    if (sz >= size) return;
    grow(size);
    for (uint32_t i = sz; i != size; i++) new (&data[i]) T();
    sz = size; }

template<class T>
void vec<T>::myCopy(const vec<T>& other) {
    assert(sz == 0);
    grow(other.size());
    for (uint32_t i = sz; i != other.size(); i++) new (&data[i]) T(other[i]);
    sz = other.size(); }

template<class T>
void vec<T>::clear(bool dealloc) {
    if (data != NULL){
        for (uint32_t i = 0; i != sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) {
            free(data);
            data = NULL;
            cap = 0;
        }
    }
}

}

#endif //__VEC_H__

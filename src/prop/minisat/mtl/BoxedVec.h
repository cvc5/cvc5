/*******************************************************************************************[Vec.h]
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

#ifndef BoxedVec_h
#define BoxedVec_h

#include <cstdlib>
#include <cassert>
#include <new>

//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)

template<class T>
class bvec {

    static inline int imin(int x, int y) {
        int mask = (x-y) >> (sizeof(int)*8-1);
        return (x&mask) + (y&(~mask)); }

    static inline int imax(int x, int y) {
        int mask = (y-x) >> (sizeof(int)*8-1);
        return (x&mask) + (y&(~mask)); }

    struct Vec_t {
        int sz;
        int cap;
        T   data[0];

        static Vec_t* alloc(Vec_t* x, int size){
            x = (Vec_t*)realloc((void*)x, sizeof(Vec_t) + sizeof(T)*size);
            x->cap = size;
            return x;
        }
        
    };

    Vec_t* ref;

    static const int init_size = 2;
    static int   nextSize (int current) { return (current * 3 + 1) >> 1; }
    static int   fitSize  (int needed)  { int x; for (x = init_size; needed > x; x = nextSize(x)); return x; }

    void fill (int size) {
        assert(ref != NULL);
        for (T* i = ref->data; i < ref->data + size; i++)
            new (i) T();
    }

    void fill (int size, const T& pad) {
        assert(ref != NULL);
        for (T* i = ref->data; i < ref->data + size; i++)
            new (i) T(pad);
    }

    // Don't allow copying (error prone):
    altvec<T>&  operator = (altvec<T>& other) { assert(0); }
    altvec (altvec<T>& other)                  { assert(0); }

public:
    void     clear  (bool dealloc = false) { 
        if (ref != NULL){
            for (int i = 0; i < ref->sz; i++) 
                (*ref).data[i].~T();

            if (dealloc) { 
                free(ref); ref = NULL; 
            }else 
                ref->sz = 0;
        } 
    }

    // Constructors:
    altvec(void)                   : ref (NULL) { }
    altvec(int size)               : ref (Vec_t::alloc(NULL, fitSize(size))) { fill(size);      ref->sz = size; }
    altvec(int size, const T& pad) : ref (Vec_t::alloc(NULL, fitSize(size))) { fill(size, pad); ref->sz = size; }
   ~altvec(void) { clear(true); }

    // Ownership of underlying array:
    operator T*       (void)           { return ref->data; }     // (unsafe but convenient)
    operator const T* (void) const     { return ref->data; }

    // Size operations:
    int      size   (void) const       { return ref != NULL ? ref->sz : 0; }

    void     pop    (void)             { assert(ref != NULL && ref->sz > 0); int last = --ref->sz; ref->data[last].~T(); }
    void     push   (const T& elem) {
        int size = ref != NULL ? ref->sz  : 0;
        int cap  = ref != NULL ? ref->cap : 0;
        if (size == cap){
            cap = cap != 0 ? nextSize(cap) : init_size;
            ref = Vec_t::alloc(ref, cap); 
        }
        //new (&ref->data[size]) T(elem); 
        ref->data[size] = elem; 
        ref->sz = size+1; 
    }

    void     push   () {
        int size = ref != NULL ? ref->sz  : 0;
        int cap  = ref != NULL ? ref->cap : 0;
        if (size == cap){
            cap = cap != 0 ? nextSize(cap) : init_size;
            ref = Vec_t::alloc(ref, cap); 
        }
        new (&ref->data[size]) T(); 
        ref->sz = size+1; 
    }

    void     shrink (int nelems)             { for (int i = 0; i < nelems; i++) pop(); }
    void     shrink_(int nelems)             { for (int i = 0; i < nelems; i++) pop(); }
    void     growTo (int size)               { while (this->size() < size) push(); }
    void     growTo (int size, const T& pad) { while (this->size() < size) push(pad); }
    void     capacity (int size)             { growTo(size); }

    const T& last  (void) const              { return ref->data[ref->sz-1]; }
    T&       last  (void)                    { return ref->data[ref->sz-1]; }

    // Vector interface:
    const T& operator [] (int index) const  { return ref->data[index]; }
    T&       operator [] (int index)        { return ref->data[index]; }

    void copyTo(altvec<T>& copy) const { copy.clear(); for (int i = 0; i < size(); i++) copy.push(ref->data[i]); }
    void moveTo(altvec<T>& dest) { dest.clear(true); dest.ref = ref; ref = NULL; }

};


#endif

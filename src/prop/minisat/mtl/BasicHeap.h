/******************************************************************************************[Heap.h]
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

#ifndef BasicHeap_h
#define BasicHeap_h

#include "Vec.h"

//=================================================================================================
// A heap implementation with support for decrease/increase key.


template<class Comp>
class BasicHeap {
    Comp     lt;
    vec<int> heap;     // heap of ints

    // Index "traversal" functions
    static inline int left  (int i) { return i*2+1; }
    static inline int right (int i) { return (i+1)*2; }
    static inline int parent(int i) { return (i-1) >> 1; }

    inline void percolateUp(int i)
    {
        int x = heap[i];
        while (i != 0 && lt(x, heap[parent(i)])){
            heap[i]          = heap[parent(i)];
            i                = parent(i);
        }
        heap   [i] = x;
    }


    inline void percolateDown(int i)
    {
        int x = heap[i];
        while (left(i) < heap.size()){
            int child = right(i) < heap.size() && lt(heap[right(i)], heap[left(i)]) ? right(i) : left(i);
            if (!lt(heap[child], x)) break;
            heap[i]          = heap[child];
            i                = child;
        }
        heap[i] = x;
    }


    bool heapProperty(int i) {
        return i >= heap.size()
            || ((i == 0 || !lt(heap[i], heap[parent(i)])) && heapProperty(left(i)) && heapProperty(right(i))); }


  public:
    BasicHeap(const C& c) : comp(c) { }

    int  size      ()                     const { return heap.size(); }
    bool empty     ()                     const { return heap.size() == 0; }
    int  operator[](int index)            const { return heap[index+1]; }
    void clear     (bool dealloc = false)       { heap.clear(dealloc); }
    void insert    (int n)                      { heap.push(n); percolateUp(heap.size()-1); }


    int  removeMin() {
        int r   = heap[0];
        heap[0] = heap.last();
        heap.pop();
        if (heap.size() > 1) percolateDown(0);
        return r; 
    }


    // DEBUG: consistency checking
    bool heapProperty() {
        return heapProperty(1); }


    // COMPAT: should be removed
    int  getmin    ()      { return removeMin(); }
};


//=================================================================================================
#endif

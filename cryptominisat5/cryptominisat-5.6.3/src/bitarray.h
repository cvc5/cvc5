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

#ifndef BITARRAY_H
#define BITARRAY_H

//#define DEBUG_BITARRAY

#include <string.h>
#include <cassert>
#include "constants.h"
#include <stdlib.h>


namespace CMSat {

class BitArray
{
public:
    ~BitArray()
    {
        free(mp);
    }

    BitArray()
    {}

    BitArray(const BitArray& other)
    {
        *this = other;
    }

    BitArray& operator=(const BitArray& b)
    {
        if (size != b.size) {
            mp = (uint64_t*)realloc(mp, b.size*sizeof(uint64_t));
            assert(mp != NULL);
            size = b.size;
        }
        memcpy(mp, b.mp, size*sizeof(uint64_t));

        return *this;
    }

    void resize(uint32_t _size, const bool fill)
    {
        _size = _size/64 + (bool)(_size%64);
        if (size != _size) {
            mp = (uint64_t*)realloc(mp, _size*sizeof(uint64_t));
            assert(mp != NULL);
            size = _size;
        }
        if (fill) setOne();
        else setZero();
    }

    inline bool isZero() const
    {
        const uint64_t*  mp2 = (const uint64_t*)mp;

        for (uint32_t i = 0; i < size; i++) {
            if (mp2[i]) return false;
        }
        return true;
    }

    inline void setZero()
    {
        if (size != 0) {
            memset(mp, 0, size*sizeof(uint64_t));
        }
    }

    inline void setOne()
    {
        if (size != 0) {
            memset(mp, 0xff, size*sizeof(uint64_t));
        }
    }

    inline void clearBit(const uint32_t i)
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        mp[i/64] &= ~((uint64_t)1 << (i%64));
    }

    inline void setBit(const uint32_t i)
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        mp[i/64] |= ((uint64_t)1 << (i%64));
    }

    inline bool operator[](const uint32_t& i) const
    {
        #ifdef DEBUG_BITARRAY
        assert(size*64 > i);
        #endif

        return (mp[i/64] >> (i%64)) & 1;
    }

    inline uint32_t getSize() const
    {
        return size*64;
    }

private:

    uint32_t size = 0;
    uint64_t* mp = NULL;
};

} //end namespace

#endif //BITARRAY_H


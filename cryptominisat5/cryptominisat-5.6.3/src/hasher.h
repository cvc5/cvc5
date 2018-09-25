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

#include "solvertypes.h"

namespace CMSat
{

// Use 1G extra for clause re-learning bitmap.
static const uint32_t hash_bits = 28;
static const uint32_t hash_size = 1 << hash_bits;
static const uint32_t hash_mask = hash_size - 1;

static inline uint64_t rotl(uint64_t x, uint64_t n)
{
        return (x << n) | (x >> (8 * sizeof(x) - n));
}

#define HASH_MULT_CONST 0x61C8864680B583EBULL

static inline uint64_t clause_hash(vector<Lit> &clause)
{
    //assert((sizeof(Lit) * clause.size()) % sizeof(unsigned long) == 0);

    uint64_t x = 0;
    uint64_t y = 0;

    for (const Lit l: clause) {
        x = x ^ l.toInt();
        y = x ^ y;
        x = rotl(x, 12);
        x = x + y;
        y = rotl(y, 45);
        y = 9 * y;
    }

    y = y ^ (x * HASH_MULT_CONST);
    y = y * HASH_MULT_CONST;
    return y;
}

}

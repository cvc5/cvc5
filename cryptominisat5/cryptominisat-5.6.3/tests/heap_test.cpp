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

#include "gtest/gtest.h"

#include "cryptominisat5/cryptominisat.h"

#include "src/heap.h"

using CMSat::Heap;

struct Comp
{
    bool operator()(uint32_t a, uint32_t b) const
    {
        return a < b;
    }
};

TEST(heap_minim, simple)
{
    Comp cmp;
    Heap<Comp> heap(cmp);
    heap.insert(1);
    heap.insert(2);
    heap.insert(3);
    EXPECT_EQ( heap.heap_property(), true);
}

TEST(heap_minim, empty)
{
    Comp cmp;
    Heap<Comp> heap(cmp);
    heap.insert(1);
    heap.insert(2);
    EXPECT_EQ(heap.removeMin(), 1);
    EXPECT_EQ(heap.removeMin(), 2);
    EXPECT_EQ( heap.heap_property(), true);
}

TEST(heap_minim, empty2)
{
    Comp cmp;
    Heap<Comp> heap(cmp);
    heap.insert(1);
    heap.insert(2);
    heap.insert(3);
    EXPECT_EQ(heap.removeMin(), 1);
    EXPECT_EQ(heap.removeMin(), 2);
    EXPECT_EQ(heap.removeMin(), 3);
    EXPECT_EQ( heap.heap_property(), true);
}

TEST(heap_minim, empty_lots)
{
    Comp cmp;
    Heap<Comp> heap(cmp);
    for(size_t i = 0; i < 100; i++) {
        heap.insert(99-i);
        EXPECT_EQ( heap.heap_property(), true);
    }
    for(int i = 0; i < 100; i++) {
        EXPECT_EQ(heap.removeMin(), i);
        EXPECT_EQ(heap.heap_property(), true);
    }
}

TEST(heap_minim, inserted_inside)
{
    Comp cmp;
    Heap<Comp> heap(cmp);
    heap.insert(10);
    heap.insert(20);
    EXPECT_EQ(heap.inHeap(10), true);
    EXPECT_EQ(heap.inHeap(20), true);
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}

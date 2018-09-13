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

#ifndef __MYSTACK_H__
#define __MYSTACK_H__

#include <vector>
using std::vector;

namespace CMSat {

template<class T>
class MyStack
{
public:
    void clear()
    {
        inter.clear();
    }

    bool empty() const
    {
        return inter.empty();
    }

    void pop()
    {
        assert(!inter.empty());
        inter.resize(inter.size()-1);
    }

    const T top() const
    {
        return inter.back();
    }

    void push(const T& data)
    {
        inter.push_back(data);
    }

    size_t capacity() const
    {
        return inter.capacity();
    }

    size_t mem_used() const
    {
        return capacity()*sizeof(T);
    }

private:
    vector<T> inter;
};

}

#endif //__MYSTACK_H__

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

#ifndef _XOR_H_
#define _XOR_H_

#include "solvertypes.h"

#include <vector>
#include <set>
#include <iostream>
#include <algorithm>

using std::vector;

namespace CMSat {

class Xor
{
public:
    Xor() : rhs(false)
    {}
    template<typename T>
    Xor(const T& cl, const bool _rhs) :
        rhs(_rhs)
    {
        for (uint32_t i = 0; i < cl.size(); i++) {
            vars.push_back(cl[i].var());
        }
    }

    Xor(const vector<uint32_t>& _vars, const bool _rhs) :
        rhs(_rhs)
        , vars(_vars)
    {
    }

    void sort()
    {
        std::sort(vars.begin(), vars.end());
    }

    vector<uint32_t>::const_iterator begin() const
    {
        return vars.begin();
    }

    vector<uint32_t>::const_iterator end() const
    {
        return vars.end();
    }

    vector<uint32_t>::iterator begin()
    {
        return vars.begin();
    }

    vector<uint32_t>::iterator end()
    {
        return vars.end();
    }

    bool operator==(const Xor& other) const
    {
        return (rhs == other.rhs && vars == other.vars);
    }

    bool operator!=(const Xor& other) const
    {
        return !operator==(other);
    }

    bool operator<(const Xor& other) const
    {
        uint64_t i = 0;
        while(i < other.size() && i < size()) {
            if (other[i] != vars[i]) {
                return (other[i] > vars[i]);
            }
            i++;
        }

        if (other.size() != size()) {
            return size() < other.size();
        }
        return false;
    }

    const uint32_t& operator[](const uint32_t at) const
    {
        return vars[at];
    }

    uint32_t& operator[](const uint32_t at)
    {
        return vars[at];
    }

    void resize(const uint32_t newsize)
    {
        vars.resize(newsize);
    }

    vector<uint32_t>& get_vars()
    {
        return vars;
    }

    const vector<uint32_t>& get_vars() const
    {
        return vars;
    }

    size_t size() const
    {
        return vars.size();
    }
    bool rhs;

private:
    vector<uint32_t> vars;
};

inline std::ostream& operator<<(std::ostream& os, const Xor& thisXor)
{
    for (uint32_t i = 0; i < thisXor.size(); i++) {
        os << Lit(thisXor[i], false);

        if (i+1 < thisXor.size())
            os << " + ";
    }
    os << " =  " << std::boolalpha << thisXor.rhs << std::noboolalpha;

    return os;
}

}

#endif //_XOR_H_

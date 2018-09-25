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

#ifndef __VARUPDATE_HELPER_H__
#define __VARUPDATE_HELPER_H__

#include "solvertypes.h"
#include <iostream>
#include <set>

namespace CMSat {

uint32_t getUpdatedVar(uint32_t toUpdate, const vector< uint32_t >& mapper);
Lit getUpdatedLit(Lit toUpdate, const vector< uint32_t >& mapper);

template<typename T>
void updateArray(T& toUpdate, const vector< uint32_t >& mapper)
{
    T backup = toUpdate;
    for(size_t i = 0; i < toUpdate.size(); i++) {
        toUpdate.at(i) = backup.at(mapper.at(i));
    }
}

template<typename T>
void updateArrayRev(T& toUpdate, const vector< uint32_t >& mapper)
{
    assert(toUpdate.size() >= mapper.size());
    T backup = toUpdate;
    for(size_t i = 0; i < mapper.size(); i++) {
        toUpdate[mapper[i]] = backup[i];
    }
}

template<typename T>
void updateArrayMapCopy(T& toUpdate, const vector< uint32_t >& mapper)
{
    //assert(toUpdate.size() == mapper.size());
    T backup = toUpdate;
    for(size_t i = 0; i < toUpdate.size(); i++) {
        if (backup[i] < mapper.size()) {
            toUpdate[i] = mapper[backup[i]];
        }
    }
}

template<typename T>
void updateLitsMap(T& toUpdate, const vector< uint32_t >& mapper)
{
    for(size_t i = 0; i < toUpdate.size(); i++) {
        if (toUpdate[i].var() < mapper.size()) {
            toUpdate[i] = getUpdatedLit(toUpdate[i], mapper);
        }
    }
}

template<typename T>
void updateVarsMap(T& toUpdate, const vector< uint32_t >& mapper)
{
    for(size_t i = 0; i < toUpdate.size(); i++) {
        if (toUpdate[i] < mapper.size()) {
            toUpdate[i] = getUpdatedVar(toUpdate[i], mapper);
        }
    }
}

inline Lit getUpdatedLit(Lit toUpdate, const vector< uint32_t >& mapper)
{
    return Lit(getUpdatedVar(toUpdate.var(), mapper), toUpdate.sign());
}

inline uint32_t getUpdatedVar(uint32_t toUpdate, const vector< uint32_t >& mapper)
{
    return mapper.at(toUpdate);
}

template<typename T, typename T2>
inline void updateBySwap(T& toUpdate, T2& seen, const vector< uint32_t >& mapper)
{
    for(size_t i = 0; i < toUpdate.size(); i++) {
        if (seen.at(i)) {
            //Already updated, skip
            continue;
        }

        //Swap circularly until we reach full circle
        uint32_t var = i;
        const uint32_t origStart = var;
        while(true) {
            uint32_t swapwith = mapper.at(var);
            assert(seen.at(swapwith) == 0);
            //std::cout << "Swapping " << var << " with " << swapwith << std::endl;
            using std::swap;
            swap(toUpdate.at(var), toUpdate.at(swapwith));
            seen.at(swapwith) = 1;
            var = swapwith;

            //Full circle
            if (mapper.at(var) == origStart) {
                seen.at(mapper.at(var)) = 1;
                break;
            }
        };
    }

    //clear seen
    for(size_t i = 0; i < toUpdate.size(); i++) {
        assert(seen.at(i) == 1);
        seen.at(i) = 0;
    }
}

} //end namespace

#endif //__VARUPDATE_HELPER_H__
